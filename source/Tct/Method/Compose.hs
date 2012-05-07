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
       , composeStatic
       , composeDynamic
       , ComposeBound (..)
       , Partitioning (..)
         -- * Proof Object
       , ComposeProof (..)
       , progress
         -- * Processor
       , composeProcessor
       , Compose
       )
       where

import Data.Typeable (Typeable)
import Text.PrettyPrint.HughesPJ
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
import Termlib.Trs (RuleList(..), union, (\\))
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


data Partitioning = Static (RuleSelector ComposeBound) -- ^ Select rules statically according to a 'RuleSelector'.
                  | Dynamic  -- ^ Selection of the rules is determined by the applied processor.
 deriving (Typeable)

instance Show Partitioning where
    show Dynamic    = "dynamically selecting rules"
    show (Static s) = "statically selecting rules by '" ++ show s ++ "'"

instance AssocArgument Partitioning where 
    assoc _ = [ ("dynamic",    Dynamic) ] --TODO extend

-- Compose Processor ala Waldmann

data Compose p = ComposeProc

data ComposeProof p = ComposeProof { proofBound        :: ComposeBound 
                                   , proofPartitioning :: Partitioning 
                                   , proofSelected     :: [Rule.Rule] 
                                   , proofSubProof     :: (P.Proof p) }
                    | Inapplicable String


progress :: P.Processor p => ComposeProof p -> Bool
progress Inapplicable {} = False
progress p@(ComposeProof {}) = not (Trs.isEmpty $ stricts) && P.succeeded subproof
  where subproof = proofSubProof p
        stricts = Prob.strictComponents $ P.inputProblem $ subproof



instance (P.Processor p) => T.Transformer (Compose p) where
    type ArgumentsOf (Compose p) = Arg (Assoc Partitioning) :+: Arg (EnumOf ComposeBound) :+: Arg (Proc p)
    type ProofOf (Compose p)     = ComposeProof p

    name _              = "compose"
    instanceName inst   = show $ text "compose" <+> parens (ppsplit <> text "," <+> ppCompFn)
        where split :+: compFn :+: _ = T.transformationArgs inst
              ppsplit = text $ show split 
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
          , A.defaultValue = Dynamic
          , A.description  = unwords 
                             [ "This argument of type 'Compose.Partitioning' determines strict rules of"
                             , "problem (A). Usually, this should be set to 'Dynamic', in which case"
                             , "the given processor determines selection of rules dynamically."
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
      arg { A.name = "subprocessor"
          , A.description = unlines [ "The processor applied on subproblem (A)."]
          }

    transform inst prob = 
      case mreason of 
        Just reason -> return $ T.NoProgress $ Inapplicable reason
        Nothing -> 
          case split of 
            Dynamic -> 
              do pp <- P.solvePartial inst1 (forcedDps ++ forcedTrs) prob
                 let rDps = Trs.fromRules (P.ppRemovableDPs pp)
                     rTrs = Trs.fromRules (P.ppRemovableTrs pp)
                     sDps = Prob.strictDPs prob \\ rDps
                     sTrs = Prob.strictTrs prob \\ rTrs
                     rSubProof = P.Proof { P.inputProblem = rProb (rDps,rTrs) (sDps,sTrs)
                                         , P.appliedProcessor = inst1
                                         , P.result = P.ppResult pp }
                 return $ mkResult rSubProof (rDps,rTrs) (sDps,sTrs)
            Static s 
              | Trs.isEmpty rDps && Trs.isEmpty rTrs -> 
                return $ T.NoProgress $ Inapplicable "no rule selected"
              | otherwise -> 
                do rSubProof <- P.apply inst1 $ rProb (rDps,rTrs) (sDps,sTrs)
                   return $ mkResult rSubProof (rDps,rTrs) (sDps,sTrs)
              where rs   = rsSelect s compfn prob
                    rDps = Prob.sdp rs `Trs.union` Trs.fromRules forcedDps                    
                    rTrs = Prob.strs rs `Trs.union` Trs.fromRules forcedTrs
                    sDps = Prob.strictDPs prob \\ rDps
                    sTrs = Prob.strictTrs prob \\ rTrs
                    

        where split :+: compfn :+: inst1 = T.transformationArgs inst

              weaks   = Prob.weakComponents prob

              (forcedDps, forcedTrs) = 
                case compfn of 
                  Compose -> (fsi Prob.strictDPs, fsi Prob.strictTrs)
                    where fsi f = [ rule | rule <- Trs.rules (f prob), not (Rule.isNonSizeIncreasing rule)]
                  _       -> ([],[])

              rProb (rDps,rTrs) (sDps,sTrs) =
                Prob.sanitise $ prob { strictDPs = rDps
                                     , strictTrs = rTrs
                                     , weakTrs   = sTrs `Trs.union` weakTrs prob
                                     , weakDPs   = sDps `Trs.union` weakDPs prob }
                      

              mkResult rSubProof (rDps,rTrs) (sDps,sTrs)
                  | progress tproof = T.Progress tproof  (enumeration'  [sProb])
                  | otherwise       = T.NoProgress tproof
                  where tproof = ComposeProof compfn split (forcedDps ++ forcedTrs) rSubProof
                        sProb 
                          | compfn == Add = 
                            prob { strictTrs  = sTrs
                                 , strictDPs  = sDps
                                 , weakTrs    = rTrs `union` Prob.weakTrs prob
                                 , weakDPs    = rDps `union` Prob.weakDPs prob }
                          | otherwise = 
                              prob { startTerms = TermAlgebra $ F.symbols $ Prob.signature prob
                                   , strictTrs  = sTrs
                                   , strictDPs  = sDps }
                                                       
              mreason 
                | compfn /= Add && Trs.isDuplicating (Prob.allComponents prob) = Just "some rule is duplicating"
                | compfn /= Add &&  not (Trs.isNonSizeIncreasing weaks)          = Just "some weak rule is size increasing"
                | otherwise = 
                  case compfn of 
                    Add              -> Nothing
                    Mult | sizeinc   -> Just "some strict rule is size increasing"
                         | otherwise -> Nothing
                    Compose          -> Nothing
                where sizeinc = not $ Trs.isNonSizeIncreasing $ Prob.strictComponents prob
                                 

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
          
      pprintTProof _ _ (Inapplicable reason) _ = paragraph ("We cannot use 'composeCompose' since " 
                                                            ++ reason ++ ".")
      pprintTProof t prob (tproof@(ComposeProof compfn split stricts rSubProof)) _ = 
        if progress tproof 
        then paragraph ("We use the processor " 
                        ++ tName ++ " to orient following rules strictly. "
                        ++ "These rules were chosen according to '" ++ show split ++ "'.")
             $+$ text ""
             $+$ pptrs "DPs" rDPs
             $+$ pptrs "Trs" rTrs
             $+$ text ""
             $+$ paragraph ("The induced complexity of " ++ tName ++ " on above rules is " 
                            ++ show (pprint (P.answer rSubProof)) ++ ".")
             $+$ text ""
             $+$ block' "Sub-proof" [ppSubproof]
             $+$ text ""
             $+$ paragraph( "The overall complexity is obtained by " ++ compName ++ ".")
        else if null stricts 
             then paragraph "We fail to orient any rules."
                  $+$ text ""
                  $+$ ppSubproof
             else paragraph "We have tried to orient orient following rules strictly:"
                  $+$ text ""
                  $+$ pptrs "Strict Rules" (Trs stricts)
            where compName = case compfn of 
                                 Add     -> "addition"
                                 Mult    -> "multiplication"
                                 Compose -> "composition"
                  rDPs = Prob.strictDPs $ P.inputProblem $ rSubProof
                  rTrs = Prob.strictTrs $ P.inputProblem $ rSubProof
                  sig = Prob.signature prob
                  vars = Prob.variables prob
                  tName = "'" ++ T.instanceName t ++ "'"
                  pptrs = pprintNamedTrs sig vars
                  ppSubproof = P.pprintProof rSubProof P.ProofOutput
                  
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
compose :: (P.Processor p1) => Partitioning -> ComposeBound -> P.InstanceOf p1 -> T.TheTransformer (Compose p1)
compose split compfn sub = T.Transformation ComposeProc `T.withArgs` (split :+: compfn :+: sub)

-- | @composeDynamic == compose Dynamic@.
composeDynamic :: (P.Processor p1) => ComposeBound -> P.InstanceOf p1 -> T.TheTransformer (Compose p1)
composeDynamic = compose Dynamic
-- | @composeStatic rs = compose (Static rs)@.
composeStatic :: (P.Processor p1) => (RuleSelector ComposeBound) -> ComposeBound -> P.InstanceOf p1 -> T.TheTransformer (Compose p1)
composeStatic rs = compose (Static rs)

