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
import Tct.Utils.PPrint (block')
import Tct.Processor.Args.Instances
import Tct.Processor (ComplexityProof (..), certificate)
import qualified Tct.Certificate as Cert

import Termlib.Trs.PrettyPrint (pprintNamedTrs)
import Termlib.Utils (PrettyPrintable (..), paragraph)
import Termlib.Trs (RuleList(..), union, (\\))
import qualified Termlib.Trs as Trs
import qualified Termlib.Rule as Rule
import Termlib.Problem (Problem (..), StartTerms (..))
import qualified Termlib.Problem as Prob
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

data ComposeProof p = ComposeProof ComposeBound Partitioning [Rule.Rule] (Either (P.Proof p) (P.PartialProof (P.ProofOf p)))
                    | Inapplicable String


progress :: P.Processor p => ComposeProof p -> Bool
progress (ComposeProof _ _ _ esp) = 
  case esp of 
    Left sp1  -> not (Trs.isEmpty $ Prob.strictComponents $ P.inputProblem sp1) && P.succeeded sp1
    Right sp1 -> not (null (P.ppRemovableTrs sp1) && null (P.ppRemovableDPs sp1))
progress Inapplicable {} = False


instance (P.Processor p) => T.Transformer (Compose p) where
    type T.ArgumentsOf (Compose p) = Arg (Assoc Partitioning) :+: Arg (EnumOf ComposeBound) :+: Arg (Proc p)
    type T.ProofOf (Compose p)     = ComposeProof p

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
              do sp1 <- P.solvePartial inst1 (forcedDps ++ forcedTrs)  prob
                 let rTrs = Trs.fromRules (P.ppRemovableTrs sp1)
                     sTrs = Prob.strictTrs prob \\ rTrs
                     rDps = Trs.fromRules (P.ppRemovableDPs sp1)
                     sDps = Prob.strictDPs prob \\ rDps
                 return $ mkResult (Right sp1) (rDps, sDps) (rTrs, sTrs)                         
            Static s 
              | Trs.isEmpty rDps && Trs.isEmpty rTrs -> return $ T.NoProgress $ Inapplicable "no rule selected"
              | otherwise -> 
                do sp1 <- P.apply inst1 prob1
                   return $ mkResult (Left sp1) (rDps, sDps) (rTrs, sTrs)                         
              where rs             = rsSelect s compfn prob
                    rDps           = Prob.sdp rs `Trs.union` Trs.fromRules forcedDps
                    rTrs           = Prob.strs rs `Trs.union` Trs.fromRules forcedTrs
                    sTrs           = strictTrs prob Trs.\\ rTrs
                    sDps           = strictDPs prob Trs.\\ rDps
                    prob1 = Prob.sanitise $ prob { strictDPs = rDps
                                                 , strictTrs = rTrs
                                                 , weakTrs   = sTrs `Trs.union` weakTrs prob
                                                 , weakDPs   = sDps `Trs.union` weakDPs prob }

        where split :+: compfn :+: inst1 = T.transformationArgs inst

              weaks   = Prob.weakComponents prob

              (forcedDps, forcedTrs) = case compfn of 
                                         Compose -> (fsi Prob.strictDPs, fsi Prob.strictTrs)
                                             where fsi f = [ rule | rule <- Trs.rules (f prob), not (Rule.isNonSizeIncreasing rule)]
                                         _       -> ([],[])

              mkResult esp1 (rDPs, sDPs) (rTrs, sTrs)
                  | progress tproof = T.Progress tproof  (enumeration'  [prob2])
                  | otherwise       = T.NoProgress tproof
                  where tproof = ComposeProof compfn split (forcedDps ++ forcedTrs) esp1
                        prob2 | compfn == Add = prob { strictTrs  = sTrs
                                                     , strictDPs  = sDPs
                                                     , weakTrs    = rTrs `union` Prob.weakTrs prob
                                                     , weakDPs    = rDPs `union` Prob.weakDPs prob }
                              | otherwise    = prob { startTerms = TermAlgebra
                                                    , strictTrs  = sTrs
                                                    , strictDPs  = sDPs }
                                                       
              mreason | compfn /= Add && Trs.isDuplicating (Prob.allComponents prob) = Just "some rule is duplicating"
                      | compfn /= Add &&  not (Trs.isNonSizeIncreasing weaks)          = Just "some weak rule is size increasing"
                      | otherwise = 
                        case compfn of 
                          Add              -> Nothing
                          Mult | sizeinc   -> Just "some strict rule is size increasing"
                               | otherwise -> Nothing
                          Compose          -> Nothing
                where sizeinc = not $ Trs.isNonSizeIncreasing $ Prob.strictComponents prob
                                 

instance P.Processor p => T.TransformationProof (Compose p) where
      answer proof = case (T.transformationProof proof, T.subProofs proof)  of 
                     (ComposeProof compfn _ _ esp1, [(_,sp2)]) -> mkAnswer compfn esp1 sp2
                     _                                         -> P.MaybeAnswer
        where mkAnswer compfn esp1 sp2 | success   = P.CertAnswer $ Cert.certified (Cert.constant, ub)
                                       | otherwise = P.MaybeAnswer
                  where success = case (either answer answer esp1, answer sp2) of
                                    (P.CertAnswer _, P.CertAnswer _) -> True
                                    _                                -> False
                        ub = case compfn of 
                               Add     -> ub1 `Cert.add` ub2
                               Mult    -> ub1 `Cert.mult` ub2
                               Compose -> ub1 `Cert.mult` (ub2 `Cert.compose` (Cert.poly (Just 1) `Cert.add` ub1))
                        ub1 = either ubound ubound esp1
                        ub2 = ubound sp2
                        ubound :: P.ComplexityProof p => p -> Cert.Complexity
                        ubound p = Cert.upperBound $ certificate p
      pprintTProof _ _ (Inapplicable reason) _ = paragraph ("We cannot use 'composeCompose' since " 
                                                            ++ reason ++ ".")
      pprintTProof t prob (tproof@(ComposeProof compfn split stricts esp1)) _ = 
        if progress tproof 
        then paragraph ("We use the processor " 
                        ++ tName ++ " to orient following rules strictly. "
                        ++ "These rules were chosen according to '" ++ show split ++ "'.")
             $+$ text ""
             $+$ pptrs "DPs" rDPs
             $+$ pptrs "Trs" rTrs
             $+$ text ""
             $+$ paragraph ("The induced complexity of" ++ tName ++ " on above rules is " 
                            ++ show (pprint (either P.answer P.answer esp1)) ++ ".")
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
                  rDPs = either (Prob.strictDPs . P.inputProblem) (Trs . P.ppRemovableDPs) esp1
                  rTrs = either (Prob.strictTrs . P.inputProblem) (Trs . P.ppRemovableTrs) esp1
                  sig = Prob.signature prob
                  vars = Prob.variables prob
                  tName = "'" ++ T.instanceName t ++ "'"
                  pptrs = pprintNamedTrs sig vars
                  ppSubproof = either (\p -> P.pprintProof p P.ProofOutput) (\p -> P.pprintProof p P.ProofOutput) esp1

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

