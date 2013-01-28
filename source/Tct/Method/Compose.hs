{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DeriveDataTypeable #-}

{- | 
Module      :  Tct.Method.Compose
Copyright   :  (c) Martin Avanzini <martin.avanzini@uibk.ac.at>, 
               Georg Moser <georg.moser@uibk.ac.at>, 
               Andreas Schnabl <andreas.schnabl@uibk.ac.at>
License     :  LGPL (see COPYING)

Maintainer  :  Martin Avanzini <martin.avanzini@uibk.ac.at>
Stability   :  unstable
Portability :  unportable      

This module provides the /compose/ transformation.
-}


module Tct.Method.Compose 
       (
         decompose
       , decomposeDynamic
       , decomposeStatic         
       , DecomposeBound (..)
         -- * Proof Object
       , DecomposeProof (..)
       , progress
         -- * Processor
       , decomposeProcessor
       , Decompose
       , greedy
       )
       where

import Control.Monad (liftM)
import Data.Typeable (Typeable)
import Text.PrettyPrint.HughesPJ
import qualified Text.PrettyPrint.HughesPJ as PP
import Data.Maybe (fromMaybe)
import qualified Tct.Processor as P
import qualified Tct.Processor.Transformations as T
import Tct.Processor.Args
import qualified Tct.Processor.Args as A
import Tct.Utils.Enum (enumeration',enumeration,find)
import qualified Tct.Utils.Xml as Xml
import Tct.Utils.PPrint (block')
import Tct.Processor.Args.Instances
import Tct.Processor (certificate)
import qualified Tct.Certificate as Cert

import Termlib.Trs.PrettyPrint (pprintNamedTrs)
import Termlib.Utils (PrettyPrintable (..), paragraph)
import Termlib.Trs (union, (\\))
import qualified Termlib.Trs as Trs
import qualified Termlib.Rule as Rule
import Termlib.Problem (Problem (..), StartTerms (..))
import qualified Termlib.Problem as Prob
import qualified Termlib.FunctionSymbol as F
import Tct.Method.RuleSelector
-- import Termlib.Term (..)
-- static partitioning

data DecomposeBound = Add  -- ^ obtain bound by addition
                    | Mult -- ^ obtain bound by multiplication
                    | Compose  -- ^ obtain bound by composition
  deriving (Bounded, Ord, Eq, Show, Typeable, Enum) 


-- Decompose Processor ala Zankl/Korp and Waldmann
data Decompose p = DecomposeProc
data DecomposeProof p = DecomposeProof 
                        { proofBound          :: DecomposeBound 
                        , proofSelector       :: ExpressionSelector
                        , proofOrientedStrict :: [Rule.Rule]
                        , proofSubProof       :: (P.Proof p) }
                      | DecomposeStaticProof { proofBound :: DecomposeBound
                                             , proofSelectedTrs :: Trs.Trs
                                             , proofSelectedDPs :: Trs.Trs
                                             , proofSubProblems :: (Problem, Problem)}
                      | Inapplicable String


progress :: P.Processor p => DecomposeProof p -> Bool
progress Inapplicable {} = False
progress p@(DecomposeProof {}) = not (Trs.isEmpty $ stricts) && P.succeeded subproof
  where subproof = proofSubProof p
        stricts = Prob.strictComponents $ P.inputProblem $ subproof
progress p@(DecomposeStaticProof {}) = not (trivial sProb) && not (trivial rProb) 
  where trivial = Trs.isEmpty . Prob.strictComponents
        (sProb,rProb) = proofSubProblems p



instance (P.Processor p) => T.Transformer (Decompose p) where
    type ArgumentsOf (Decompose p) = Arg (Assoc ExpressionSelector) :+: Arg (EnumOf DecomposeBound) :+: Arg Bool :+: Arg (Maybe (Proc p))
    type ProofOf (Decompose p)     = DecomposeProof p

    name _              = "decompose"
    instanceName inst   = show $ text "decompose" <+> parens ppCompFn
        where _ :+: compFn :+: _ = T.transformationArgs inst
              -- ppsplit = text $ show split 
              ppCompFn = case compFn of 
                           Add  -> text "addition"
                           Mult -> text "multiplication"
                           Compose -> text "composition"

    description _ = 
      [ unwords 
        [ "This transformation implements techniques for splitting the complexity problem"
        , "into two complexity problems (A) and (B) so that the complexity of the input problem" 
        , "can be estimated by the complexity of the transformed problem."
        , "The processor closely follows the ideas presented in"
        , "/Complexity Bounds From Relative Termination Proofs/"
        , "(<http://www.imn.htwk-leipzig.de/~waldmann/talk/06/rpt/rel/main.pdf>)" ]
      ]
    arguments _ = 
      opt { A.name         = "split" 
          , A.defaultValue = selAnyOf selStricts
          , A.description  = unwords 
                             [ "This argument of type 'Compose.Partitioning' determines strict rules of"
                             , "problem (A). The default is to orient some strict rule."
                             ]
          }
      :+: 
      opt { A.name = "allow"
          , A.defaultValue = Add
          , A.description = unwords 
                            [ "This argument type 'Compose.DecomposeBound' determines"
                            , "how the complexity certificate should be obtained from subproblems (A) and (B)."
                            , "Consequently, this argument also determines the shape of (B)."
                            , "The third argument defines a processor that is applied on problem (A)."
                            , "If this processor succeeds, the input problem is transformed into (B)."
                            , "Note that for decompose bound 'Mult' the transformation only succeeds"
                            , "if applied to non size-increasing Problems."
                            ] 
          }
      :+: 
      opt { A.name = "greedy"
          , A.defaultValue = False
          , A.description = unwords 
                            [ "Search to orient as many rules as possible by itterating the given subprocessor."
                            ] 
          }
      :+: 
      opt { A.name = "subprocessor"
          , A.defaultValue = Nothing
          , A.description = unlines [ "The processor applied on subproblem (A)."]
          }

    transform inst prob = 
      case (mreason, minst1) of 
        (Just reason, _) -> return $ T.NoProgress $ Inapplicable reason
        (_, Just inst1) -> do 
          pp <- P.solvePartial inst1 sel prob
          if P.failed (P.ppResult pp) || not grdy
           then return $ mkProof inst1 pp
           else mkProof inst1 `liftM` solveGreedy inst1 pp
        (_, Nothing) | progress tproof -> return $ T.Progress tproof (enumeration [('R', rProb), ('S',sProb)])
                     | otherwise       -> return $ T.NoProgress tproof
          where (rProb,sProb) = mkProb dps trs
                (dps, trs) = rules sel
                tproof = DecomposeStaticProof { proofBound = compfn
                                            , proofSelectedDPs = dps
                                            , proofSelectedTrs = trs
                                            , proofSubProblems = (rProb, sProb)}
                
        where rs :+: compfn :+: grdy :+: minst1 = T.transformationArgs inst
    
              solveGreedy inst1 pp 
                | null (remainingDPs ++ remainingTrs) = return pp
                | otherwise = do
                  pp' <- P.solvePartial inst1 sel' prob
                  if P.succeeded $ P.ppResult pp' 
                   then solveGreedy inst1 pp' 
                   else return pp  
                where remainingDPs = [r | r <- Trs.rules $ Prob.dpComponents prob
                                        , not $ r `elem` P.ppRemovableDPs pp]
                      remainingTrs = [r | r <- Trs.rules $ Prob.trsComponents prob
                                        , not $ r `elem` P.ppRemovableTrs pp]
                      sel' = P.BigAnd $ [ P.BigOr $ [P.SelectDP r | r <- remainingDPs] ++ [P.SelectTrs r | r <- remainingTrs] ]
                                           ++ [P.SelectDP r | r <- P.ppRemovableDPs pp ] ++ [P.SelectTrs r | r <- P.ppRemovableTrs pp ]
                
              selectForcedRules = P.BigAnd $ [P.SelectDP r | r <- forcedDps ] 
                                               ++ [P.SelectTrs r | r <- forcedTrs ]
                                  
              sel = P.BigAnd [ rsSelect rs prob, selectForcedRules ]
                                    
              (forcedDps, forcedTrs) = 
                case compfn of 
                  Compose -> (fsi Prob.dpComponents, fsi Prob.trsComponents)
                    where fsi f = [ rule | rule <- Trs.rules (f prob)
                                         , not (Rule.isNonSizeIncreasing rule)]
                  _       -> ([],[])
                                                                             
              mreason 
                | compfn /= Add 
                  && Trs.isDuplicating (Prob.allComponents prob) = Just "some rule is duplicating"
                | otherwise = 
                  case compfn of 
                    Add              -> Nothing
                    Mult | sizeinc   -> Just "some rule is size increasing"
                         | otherwise -> Nothing
                    Compose          -> Nothing
                where sizeinc = not $ Trs.isNonSizeIncreasing $ Prob.allComponents prob
                                 
              mkProof inst1 pp 
                | progress tproof = T.Progress tproof  (enumeration'  [sProb])
                | otherwise       = T.NoProgress tproof
                where (rProb, sProb) = mkProb (Trs.fromRules (P.ppRemovableDPs pp)) (Trs.fromRules (P.ppRemovableTrs pp))
                      tproof = DecomposeProof { proofBound = compfn 
                                              , proofSelector = rs 
                                              , proofOrientedStrict = Trs.rules (strictTrs rProb) ++ Trs.rules (strictDPs rProb)
                                              , proofSubProof = P.Proof { P.inputProblem = rProb
                                                                        , P.appliedProcessor = inst1
                                                                        , P.result = P.ppResult pp }
                                              }
                      
              mkProb dps trs = (rProb, sProb)
                where rDps = dps `Trs.intersect` Prob.strictDPs prob
                      rTrs = trs `Trs.intersect` Prob.strictTrs prob
                      sDps = Prob.strictDPs prob \\ rDps
                      sTrs = Prob.strictTrs prob \\ rTrs
                      
                      rProb = Prob.sanitise $ 
                              prob { strictDPs = rDps
                                   , strictTrs = rTrs
                                   , weakTrs   = sTrs `Trs.union` weakTrs prob
                                   , weakDPs   = sDps `Trs.union` weakDPs prob }
                          
                      sProb = Prob.sanitise $ 
                              case compfn of 
                                Add -> prob { strictTrs  = sTrs
                                            , strictDPs  = sDps
                                            , weakTrs    = rTrs `union` Prob.weakTrs prob
                                            , weakDPs    = rDps `union` Prob.weakDPs prob }
                                _ -> prob { startTerms = TermAlgebra $ F.symbols $ Prob.signature prob
                                          , strictTrs  = sTrs
                                          , strictDPs  = sDps }                  
                                  

instance P.Processor p => T.TransformationProof (Decompose p) where
      answer proof = 
        case tProof of 
          DecomposeStaticProof {} -> fromMaybe P.MaybeAnswer mans
            where mans = do
                    rProof <- find 'R' subproofs
                    sProof <- find 'S' subproofs
                    return $ mkAnswer rProof sProof
          DecomposeProof {} -> 
            case subproofs of 
              [(_,sProof)] 
                | not success -> P.MaybeAnswer 
                | otherwise   -> mkAnswer rProof sProof
                where rProof = proofSubProof tProof
                      success = progress tProof && P.succeeded sProof
              _  -> P.MaybeAnswer
          _ -> P.MaybeAnswer
            
        where tProof = T.transformationProof proof
              subproofs = T.subProofs proof
              mkAnswer :: (P.ComplexityProof p1, P.ComplexityProof p2) => p1 -> p2 -> P.Answer
              mkAnswer rProof sProof = 
                case ub of 
                  Cert.Unknown -> P.MaybeAnswer 
                  _ -> P.CertAnswer $ Cert.certified (Cert.constant, ub)
                where ub = case proofBound tProof of 
                            Add     -> rUb `Cert.add` sUb
                            Mult    -> rUb `Cert.mult` sUb
                            Compose -> rUb `Cert.mult` (sUb `Cert.compose` (Cert.poly (Just 1) `Cert.add` rUb))
                      rUb = ubound rProof
                      sUb = ubound sProof
                      ubound p = Cert.upperBound $ certificate p                        
              

      pprintTProof _ _ (Inapplicable reason) _ = paragraph ("We cannot use 'decompose' since " 
                                                            ++ reason ++ ".")
      pprintTProof _ prob (tproof@(DecomposeProof compfn _ stricts rSubProof)) _ = 
        if progress tproof 
        then paragraph ("We use the processor " 
                        ++ pName ++ " to orient following rules strictly.")
                        -- ++ "These rules were chosen according to '" ++ show split ++ "'.")
             $+$ text ""
             $+$ pptrs "DPs" rDPs
             $+$ pptrs "Trs" rTrs
             $+$ text ""
             $+$ paragraph ( show $ 
                             text "The induced complexity on above rules (modulo remaining rules) is" 
                             <+> pprint (P.answer rSubProof) <+> text "." 
                             <+> if compfn == Add 
                                  then text "These rules are moved into the corresponding weak component(s)."
                                  else text "These rules are removed from the problem."
                             <+> case compfn of
                                   Add -> PP.empty 
                                   Mult -> text "Note that no rule is size-increasing."
                                   Compose -> text " Note that none of the weakly oriented rules is size-increasing."
                             <+> text "The overall complexity is obtained by" <+> text compName <+> text ".")
             $+$ text ""
             $+$ block' "Sub-proof" [ppSubproof]
             $+$ text ""
             $+$ text "We return to the main proof."
             
        else if null stricts 
             then paragraph "We fail to orient any rules."
             else paragraph "We failed to orient at least the following rules strictly:"
                  $+$ text ""
                  $+$ pptrs "Strict Rules" (Trs.fromRules stricts)
            where compName = case compfn of 
                                 Add     -> "addition"
                                 Mult    -> "multiplication"
                                 Compose -> "composition"
                  rDPs = Prob.strictDPs $ P.inputProblem $ rSubProof
                  rTrs = Prob.strictTrs $ P.inputProblem $ rSubProof
                  sig = Prob.signature prob
                  vars = Prob.variables prob
                  pName = "'" ++ P.instanceName (P.appliedProcessor rSubProof) ++ "'"
                  pptrs = pprintNamedTrs sig vars
                  ppSubproof = P.pprintProof (P.result rSubProof) P.ProofOutput
                  
      pprintTProof _ _ (tproof@(DecomposeStaticProof compfn _ _ (rProb,sProb))) _ = 
        if progress tproof 
         then paragraph ("We analyse the complexity of following sub-problems (A) and (B):")
             $+$ text ""
             $+$ block' "Problem (A)" [pprint rProb]
             $+$ text ""             
             $+$ (case compfn of
                     Add -> paragraph "Problem (B) is obtained from the input problem by shifting strict rules from (A) into the weak component:"
                     Mult -> paragraph ("Observe that Problem (A) is non-size-increasing. "
                                        ++ "Once the complexity of (A) has been assessed, it suffices "
                                        ++ "to consider only rules whose complexity has not been estimated in (A) "
                                        ++ "resulting in the following Problem (B). Overall the certificate is obtained by multiplication.")
                     Compose -> paragraph ("Observe that weak rules from Problem (A) are non-size-increasing. "
                                          ++ "Once the complexity of (A) has been assessed, it suffices "
                                          ++ "to consider only rules whose complexity has not been estimated in (A) "
                                          ++ "resulting in the following Problem (B). Overall the certificate is obtained by composition."))
             $+$ block' "Problem (A)" [pprint rProb]
             $+$ pprint sProb
             
         else text "No rule was selected."

      tproofToXml tinst _ proof = 
        ( "compose"
        , [ Xml.elt "composeBy" [] [Xml.text compName]
          , Xml.elt "splitBy" [] [Xml.text $ show split]]
          ++ case proof of 
               Inapplicable reason -> [Xml.elt "rSubProof" [] [Xml.elt "inapplicable" [] [Xml.text reason]]]
               DecomposeProof {} -> [Xml.elt "rSubProof" [] [P.toXml $ proofSubProof proof]]
               _ -> []
        )
        where split :+: compFn :+: _ = T.transformationArgs tinst
              compName = 
                case compFn of 
                  Add     -> "addition"
                  Mult    -> "multiplication"
                  Compose -> "composition"

decomposeProcessor :: T.Transformation (Decompose P.AnyProcessor) P.AnyProcessor
decomposeProcessor = T.Transformation DecomposeProc

-- | This transformation implements techniques for splitting the complexity problem
-- into two complexity problems (A) and (B) so that the complexity of the input problem
-- can be estimated by the complexity of the transformed problem. 
-- The processor closely follows the ideas presented in
-- /Complexity Bounds From Relative Termination Proofs/
-- (<http://www.imn.htwk-leipzig.de/~waldmann/talk/06/rpt/rel/main.pdf>).
decompose :: (P.Processor p1) => ExpressionSelector -> DecomposeBound -> P.InstanceOf p1 -> T.TheTransformer (Decompose p1)
decompose split compfn sub = T.Transformation DecomposeProc `T.withArgs` (split :+: compfn :+: False :+: Just sub)

-- | @decomposeDynamic == decompose (selAnyOf selStricts)@.
decomposeDynamic :: (P.Processor p1) => DecomposeBound -> P.InstanceOf p1 -> T.TheTransformer (Decompose p1)
decomposeDynamic = decompose (selAnyOf selStricts)

-- | @decomposeStatic == decompose (selAnyOf selStricts)@.
decomposeStatic :: ExpressionSelector -> DecomposeBound -> T.TheTransformer (Decompose P.AnyProcessor)
decomposeStatic split compfn = T.Transformation DecomposeProc `T.withArgs` (split :+: compfn :+: False :+: Nothing)

greedy :: (P.Processor p1) => T.TheTransformer (Decompose p1) -> T.TheTransformer (Decompose p1)
greedy tinst = T.Transformation DecomposeProc `T.withArgs` (split :+: compfn :+: True :+: sub)
  where split :+: compfn :+: _ :+: sub = T.transformationArgs tinst