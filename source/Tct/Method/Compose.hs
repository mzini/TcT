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
         compose
       , composeDynamic
       , ComposeBound (..)
         -- * Proof Object
       , ComposeProof (..)
       , progress
         -- * Processor
       , composeProcessor
       , Compose
       , greedy
       )
       where

import Control.Monad (liftM)
import Data.Typeable (Typeable)
import Text.PrettyPrint.HughesPJ
import qualified Text.PrettyPrint.HughesPJ as PP
import Data.Typeable ()
import qualified Tct.Processor as P
import qualified Tct.Processor.Transformations as T
import Tct.Processor.Args
import qualified Tct.Processor.Args as A
import Tct.Utils.Enum (enumeration')
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

data ComposeBound = Add  -- ^ obtain bound by addition
                  | Mult -- ^ obtain bound by multiplication
                  | Compose  -- ^ obtain bound by composition
  deriving (Bounded, Ord, Eq, Show, Typeable, Enum) 


-- Compose Processor ala Zankl/Korp and Waldmann
data Compose p = ComposeProc
data ComposeProof p = ComposeProof { proofBound          :: ComposeBound 
                                   , proofSelector       :: ExpressionSelector
                                   , proofOrientedStrict :: [Rule.Rule]
                                   , proofSubProof       :: (P.Proof p) }
                    | Inapplicable String


progress :: P.Processor p => ComposeProof p -> Bool
progress Inapplicable {} = False
progress p@(ComposeProof {}) = not (Trs.isEmpty $ stricts) && P.succeeded subproof
  where subproof = proofSubProof p
        stricts = Prob.strictComponents $ P.inputProblem $ subproof



instance (P.Processor p) => T.Transformer (Compose p) where
    type ArgumentsOf (Compose p) = Arg (Assoc ExpressionSelector) :+: Arg (EnumOf ComposeBound) :+: Arg Bool :+: Arg (Proc p)
    type ProofOf (Compose p)     = ComposeProof p

    name _              = "compose"
    instanceName inst   = show $ text "compose" <+> parens ppCompFn
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
                            [ "This argument type 'Compose.ComposeBound' determines"
                            , "how the complexity certificate should be obtained from subproblems (A) and (B)."
                            , "Consequently, this argument also determines the shape of (B)."
                            , "The third argument defines a processor that is applied on problem (A)."
                            , "If this processor succeeds, the input problem is transformed into (B)."
                            , "Note that for compose bound 'Mult' the transformation only succeeds"
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
      arg { A.name = "subprocessor"
          , A.description = unlines [ "The processor applied on subproblem (A)."]
          }

    transform inst prob = 
      case mreason of 
        Just reason -> return $ T.NoProgress $ Inapplicable reason
        Nothing -> do 
          pp <- P.solvePartial inst1 (P.BigAnd [ rsSelect rs prob, selectForcedRules ]) prob
          if P.failed (P.ppResult pp) || not grdy
           then return $ mkProof pp
           else mkProof `liftM` solveGreedy pp
                
        where rs :+: compfn :+: grdy :+: inst1 = T.transformationArgs inst
    
              solveGreedy pp 
                | null (remainingDPs ++ remainingTrs) = return pp
                | otherwise = do
                  pp' <- P.solvePartial inst1 selector prob
                  if P.succeeded $ P.ppResult pp' 
                   then solveGreedy pp' 
                   else return pp  
                where remainingDPs = [r | r <- Trs.rules $ Prob.dpComponents prob
                                        , not $ r `elem` P.ppRemovableDPs pp]
                      remainingTrs = [r | r <- Trs.rules $ Prob.trsComponents prob
                                        , not $ r `elem` P.ppRemovableTrs pp]
                      selector = P.BigAnd $ [ P.BigOr $ [P.SelectDP r | r <- remainingDPs] ++ [P.SelectTrs r | r <- remainingTrs] ]
                                            ++ [P.SelectDP r | r <- P.ppRemovableDPs pp ] ++ [P.SelectTrs r | r <- P.ppRemovableTrs pp ]
                
              selectForcedRules = P.BigAnd $ [P.SelectDP r | r <- forcedDps ] 
                                               ++ [P.SelectTrs r | r <- forcedTrs ]
                                    
              (forcedDps, forcedTrs) = 
                case compfn of 
                  Compose -> (fsi Prob.dpComponents, fsi Prob.trsComponents)
                    where fsi f = [ rule | rule <- Trs.rules (f prob)
                                         , not (Rule.isNonSizeIncreasing rule)]
                  _       -> ([],[])
                                                                             
              mreason 
                | compfn /= Add 
                  && Trs.isDuplicating (Prob.allComponents prob) = Just "some rule is duplicating"
                -- | compfn /= Add 
                --   &&  not (Trs.isNonSizeIncreasing $ Prob.weakComponents prob) = Just "some weak rule is size increasing"
                | otherwise = 
                  case compfn of 
                    Add              -> Nothing
                    Mult | sizeinc   -> Just "some rule is size increasing"
                         | otherwise -> Nothing
                    Compose          -> Nothing
                where sizeinc = not $ Trs.isNonSizeIncreasing $ Prob.allComponents prob
                                 
              mkProof pp 
                | progress tproof = T.Progress tproof  (enumeration'  [sProb])
                | otherwise       = T.NoProgress tproof
                where rDps = Trs.fromRules (P.ppRemovableDPs pp) `Trs.intersect` Prob.strictDPs prob
                      rTrs = Trs.fromRules (P.ppRemovableTrs pp) `Trs.intersect` Prob.strictTrs prob
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
                                  
                      tproof = ComposeProof { proofBound = compfn 
                                            , proofSelector = rs 
                                            , proofOrientedStrict = Trs.rules rTrs ++ Trs.rules rDps 
                                            , proofSubProof = P.Proof { P.inputProblem = rProb
                                                                      , P.appliedProcessor = inst1
                                                                      , P.result = P.ppResult pp }
                                            }

instance P.Processor p => T.TransformationProof (Compose p) where
      answer proof = 
        case T.subProofs proof  of 
          [(_,sProof)] 
            | success -> P.CertAnswer $ Cert.certified (Cert.constant, ub)
              where tProof = T.transformationProof proof
                    rProof = proofSubProof tProof
                    
                    success = progress tProof && P.succeeded sProof
                    ub = 
                      case proofBound tProof of 
                        Add     -> rUb `Cert.add` sUb
                        Mult    -> rUb `Cert.mult` sUb
                        Compose -> rUb `Cert.mult` (sUb `Cert.compose` (Cert.poly (Just 1) `Cert.add` rUb))
                    rUb = ubound rProof
                    sUb = ubound sProof
                    ubound p = Cert.upperBound $ certificate p                        
          _  -> P.MaybeAnswer
          
      pprintTProof _ _ (Inapplicable reason) _ = paragraph ("We cannot use 'compose' since " 
                                                            ++ reason ++ ".")
      pprintTProof _ prob (tproof@(ComposeProof compfn _ stricts rSubProof)) _ = 
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
                                   Mult -> text "Note that all rules are non-size increasing."
                                   Compose -> text " Note that all strictly oriented rules are non-size increasing."
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
                  
      tproofToXml tinst _ proof = 
        ( "compose"
        , [ Xml.elt "composeBy" [] [Xml.text compName]
          , Xml.elt "splitBy" [] [Xml.text $ show split]
          , Xml.elt "rSubProof" [] 
            [ case proof of 
                 Inapplicable reason -> Xml.elt "inapplicable" [] [Xml.text reason]
                 ComposeProof {} -> P.toXml $ proofSubProof proof]]
        )
        where split :+: compFn :+: _ = T.transformationArgs tinst
              compName = 
                case compFn of 
                  Add     -> "addition"
                  Mult    -> "multiplication"
                  Compose -> "composition"

composeProcessor :: T.Transformation (Compose P.AnyProcessor) P.AnyProcessor
composeProcessor = T.Transformation ComposeProc

-- | This transformation implements techniques for splitting the complexity problem
-- into two complexity problems (A) and (B) so that the complexity of the input problem
-- can be estimated by the complexity of the transformed problem. 
-- The processor closely follows the ideas presented in
-- /Complexity Bounds From Relative Termination Proofs/
-- (<http://www.imn.htwk-leipzig.de/~waldmann/talk/06/rpt/rel/main.pdf>).
compose :: (P.Processor p1) => ExpressionSelector -> ComposeBound -> P.InstanceOf p1 -> T.TheTransformer (Compose p1)
compose split compfn sub = T.Transformation ComposeProc `T.withArgs` (split :+: compfn :+: False :+: sub)

-- | @composeDynamic == compose (selAnyOf selStricts)@.
composeDynamic :: (P.Processor p1) => ComposeBound -> P.InstanceOf p1 -> T.TheTransformer (Compose p1)
composeDynamic = compose (selAnyOf selStricts)

greedy :: (P.Processor p1) => T.TheTransformer (Compose p1) -> T.TheTransformer (Compose p1)
greedy tinst = T.Transformation ComposeProc `T.withArgs` (split :+: compfn :+: True :+: sub)
  where split :+: compfn :+: _ :+: sub = T.transformationArgs tinst