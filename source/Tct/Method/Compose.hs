{-
This file is part of the Tyrolean Complexity Tool (TCT).

The Tyrolean Complexity Tool is free software: you can redistribute it and/or modify
it under the terms of the GNU Lesser General Public License as published by
the Free Software Foundation, either version 3 of the License, or
(at your option) any later version.

The Tyrolean Complexity Tool is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU Lesser General Public License for more details.

You should have received a copy of the GNU Lesser General Public License
along with the Tyrolean Complexity Tool.  If not, see <http://www.gnu.org/licenses/>.
-}

{-# LANGUAGE ParallelListComp #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DeriveDataTypeable #-}

module Tct.Method.Compose where

import Data.Typeable (Typeable)
import Control.Monad (liftM,liftM2)
import Data.Either (partitionEithers)
import Data.List (intersperse)
import Text.PrettyPrint.HughesPJ

import qualified Tct.Processor as P
import qualified Tct.Processor.Standard as S
import Tct.Processor.Args
import qualified Tct.Processor.Args as A
import Tct.Processor.Args.Instances
import Tct.Processor (Answerable (..), Answer (..), Verifiable(..), ComplexityProof, succeeded, certificate)
import Tct.Certificate
import Termlib.Utils (PrettyPrintable (..), paragraph)
import Termlib.Trs (Trs(..), union, (\\))
import qualified Termlib.Trs as Trs
import Termlib.Problem (Problem (..), StartTerms (..))
import qualified Termlib.Problem as Prob
import Data.Tuple (swap)
-- static partitioning

data PartitionFn = Random | SeparateDp deriving (Show, Typeable, Ord, Enum, Eq, Bounded)

staticAssign :: PartitionFn -> Problem -> (p1, p2) -> (Problem, Problem)
staticAssign Random problem _ = ( mkProb dpssplit trssplit , mkProb (swap dpssplit) (swap trssplit))
    where trssplit = halve $ Prob.strictTrs problem
          dpssplit = halve $ Prob.strictDPs problem
          mkProb (sdps,wdps) (strs,wtrs) = problem { strictDPs = Trs sdps
                                                   , weakDPs   = Trs wdps `Trs.union` Prob.weakDPs problem
                                                   , strictTrs = Trs strs
                                                   , weakTrs   = Trs wtrs `Trs.union` Prob.weakTrs problem }
          halve (Trs rs) = partitionEithers [ if b then Left rule else Right rule 
                                                  | (b,rule) <- zip (intersperse True (repeat False)) rs]
staticAssign SeparateDp problem _ = (problem { strictDPs = Trs.empty
                                             , weakDPs   = Prob.weakDPs problem `Trs.union` Prob.strictTrs problem}
                                    , problem { strictTrs = Trs.empty
                                              , weakTrs   = Prob.weakTrs problem `Trs.union` Prob.strictTrs problem})

-- Waldmann/Hofbauer Conditions

-- MA:TODO: think about applicable predicate
wcAppliesTo :: Problem -> (Bool, String)
wcAppliesTo prob = (not isRcProblem && not isDpProblem && weakNoneSizeIncreasing, reason)
  where isDpProblem            = Prob.isDPProblem prob
        isRcProblem            = case startTerms prob of {TermAlgebra{} -> False; _ -> True}
        weakNoneSizeIncreasing = Trs.isEmpty weak || Trs.isNonSizeIncreasing weak
          where weak = weakTrs prob
        reason | isDpProblem = "the relative processor is not implemented for DP problems" 
               | isRcProblem = "the relative processor is not applicable to runtime complexity problems"
               | otherwise   = "the weak TRS is size-increasing"                   

-- Processor

data Compose p1 p2 = Compose

data ComposeProof p1 p2 = StaticPartitioned PartitionFn (P.Proof p1) (P.Proof p2)
                        | DynamicPartitioned Bool (P.PartialProof (P.ProofOf p1)) (P.Proof p2)
                        | NoRuleRemoved (P.PartialProof (P.ProofOf p1))
                        | RelativeEmpty 

instance (P.Processor p1, ComplexityProof (P.ProofOf p1) 
         , P.Processor p2, ComplexityProof (P.ProofOf p2))
    => PrettyPrintable (ComposeProof p1 p2) where
    pprint RelativeEmpty = paragraph "The strict component is empty."
    pprint (NoRuleRemoved p) = pprint p
    pprint (StaticPartitioned split proof1 proof2) = 
        paragraph (unlines [ "We have partition the strict rules into the pair (R_1,R_2) using the function "
                       , "'" ++ show split ++ "'." ])
                      $+$ text ""
                      $+$ pprint proof1
                      $+$ text ""
                      $+$ pprint proof2
    pprint (DynamicPartitioned relApplied prel subproof) = 
        pprint prel
        $+$ text ""
        $+$ paragraph (unlines [ if relApplied then "Above strictly oriented rules were removed." else "Above strict rules are moved into the weak component." 
                               , "The proof for the resulting subproblem looks as follows."])
        $+$ text ""
        $+$ pprint subproof


ub :: Answerable a => a -> Complexity
ub = upperBound . certificate . answer

instance (Answerable (P.ProofOf p1), Answerable (P.ProofOf p2)) => Answerable (ComposeProof p1 p2) where
    answer RelativeEmpty = CertAnswer $ certified (constant, constant)
    answer (NoRuleRemoved _) = MaybeAnswer
    answer (StaticPartitioned _ p1 p2) | success   = CertAnswer $ certified (unknown, ub p1 `add` ub p2)
                                       | otherwise = MaybeAnswer
        where success = succeeded p1 && succeeded p2
    answer (DynamicPartitioned relApplied  prel psub) | succeeded psub = CertAnswer $ certified (unknown, res)
                                                      | otherwise = MaybeAnswer
        where res | not relApplied = ub prel `add` ub psub
                  | otherwise    = combine (upperBound $ P.certificate prel) (upperBound $ P.certificate psub)
              r       = Trs.fromRules $ P.ppRemovableTrs prel -- MA:This case only applies with DPs are empty
              s       = strictTrs $ P.inputProblem psub
              sizeIncreasingR = Trs.isSizeIncreasing r
              sizeIncreasingS = Trs.isSizeIncreasing s
              combine ubRModS ubS | not sizeIncreasingS
                                    && not sizeIncreasingR  = ubRModS `mult` ubS
                                  | not sizeIncreasingS    = ubRModS `mult` (ubS `compose` (poly (Just 1) `add` ubRModS))
                                  | otherwise            = ubRModS `mult` (ubS `iter` ubRModS)

instance (Verifiable (P.ProofOf p1), Verifiable (P.ProofOf p2)) => Verifiable (ComposeProof p1 p2) where
    -- MA:TODO verify splitting function
    verify _ (StaticPartitioned _ p1 p2) = P.verify (P.inputProblem p1) (P.result p1)
                                           `P.andVerify` P.verify (P.inputProblem p2) (P.result p2)
    verify _ (DynamicPartitioned _ _ psub) = P.verify (P.inputProblem psub) (P.result psub)
    verify _ _                             = P.verifyOK


instance (P.Processor p1, P.Processor p2) => S.Processor (Compose p1 p2) where
    type S.ArgumentsOf (Compose p1 p2) = Arg (Maybe (EnumOf PartitionFn)) :+: Arg Bool :+: Arg (Proc p1) :+: Arg (Proc p2)
    type S.ProofOf (Compose p1 p2)     = ComposeProof p1 p2

    name Compose        = "compose"

    instanceName inst   = show $ (text $ S.name $ S.processor inst) <+> parens ppsplit
        where msplit :+: _ :+: _ :+: _ = S.processorArgs inst
              ppsplit = case msplit of 
                          Just split -> text "split with function" <+> text (show split)
                          Nothing    -> text "split according to first processor"

    description Compose = [ unwords [ "Given a TRS R, 'compose p1 p2' partitions R into a pair of TRSs (R_1,R_2)" 
                                    , "and applies processor 'p1' on the (relative) problem R_1 modulo R_2."
                                    , "Depending on the flag 'relative' the second processor 'p2' is either applied"
                                    , "on the relative problem R_2 modulo R_1 or the TRS R_2."
                                    , "In the former case the asymptotic upper-bound for the complexity of R is the worst upper-bound of R_1 modulo R_2 and R_2 modulo R_1.\n"
                                    , "In the latter case the complexity of R is computed based on the complexity"
                                    , "of R_1 modulo R_2 and the TRS R_2 as follows.\n"
                                    , "  1) if R_1 and R_2 are non-size-increasing then dc(n, ->_R) = O(dc(n, ->_R_1/R_2) * dc(n, ->_R_2))\n"
                                    , "  2) if R_2 is non-size-increasing then dc(n, ->_R) = O(dc(n, ->_R/S) * dc(n + dc(n,->_R_1/R_2), ->_R_2))\n"
                                    , "  3) otherwise dc(n, ->_R) = O(dc(n, ->_R/S) * f(n)) where f(n) denotes m-times iteration of the function \\n. dc(n,->_R_2) where m :=  dc(n,->_R_1/R_2) + 1.\n\n"
                                    , "Note that criteria 1--3 are only applied for derivational complexity analysis.\n\n"
                                    , "The processor is also applicable in the dependency pair setting and on relative input problems (without criteria 1--3)."
                                    ]
                          ]
    arguments Compose   = opt { A.name = "staticWith" 
                              , A.defaultValue = Nothing
                              , A.description = unwords ["If this argument is set then the input TRS R is partitioned into TRSs (R_1,R_2) according to the supplied argument."
                                                        , "If 'Random' is supplied, the strict TRSs R are splitted equally in size."
                                                        , "If 'SplitDP' is supplied, the first processor processes is applied to the subproblem where DPs are strict and the remaining strict rules are weak,"
                                                        , "and the second processor is applied to the inverse problem." ]}
                          :+: opt { A.name = "relative"
                                  , A.defaultValue = False
                                  , A.description = unwords [ "This flag specifies how the second component R_2 is handled by the second given processor 'p2'."
                                                            , "If this flag is set, and one of the above criteria 1--3 applies, processor 'p2' is used to estimate the complexity of R_2."
                                                            , "Otherwise, the processor 'p2' is applied on the subproblem R_2 modulo R_1."] }
                          :+: arg { A.name = "Subprocessor 1"
                                  , A.description = unlines ["The Processor to estimate the complexity of R_1 modulo R_2."]}
                          :+: arg { A.name = "Subprocessor 2"
                                  , A.description = unlines ["The Processor to estimate the complexity of R_2 modulo R_1, or respectively R_2."] }

    solve inst prob | Trs.isEmpty (Prob.strictComponents prob) = return RelativeEmpty 
                    | otherwise = case msplit of 
                                    Just split -> solveStatic split
                                    Nothing    -> solveDynamic
        where msplit :+: relative :+: inst1 :+: inst2 = S.processorArgs inst
              (relativeApplicable, _) =  wcAppliesTo prob
              solveStatic split = let (p1,p2) = staticAssign split prob (inst1, inst2)
                                  in  liftM2 (StaticPartitioned split) (P.apply inst1 p1) (P.apply inst2 p2)
              solveDynamic = do res <- P.solvePartial inst1 prob
                                let removedTrs = Trs.fromRules (P.ppRemovableTrs res)
                                    removedDPs = Trs.fromRules (P.ppRemovableDPs res)
                                    relApplied = relative && relativeApplicable
                                    subprob = case relApplied of 
                                                True  -> prob { startTerms = TermAlgebra
                                                             , strictTrs  = strictTrs prob \\ removedTrs }
                                                False -> prob { strictTrs = strictTrs prob \\ removedTrs 
                                                             , strictDPs = strictDPs prob \\ removedDPs
                                                             , weakTrs   = weakTrs prob `union` removedTrs
                                                             , weakDPs   = weakDPs prob `union` removedDPs }
                                case P.progressed res of 
                                  False -> return $ NoRuleRemoved res
                                  True  -> DynamicPartitioned relApplied res `liftM` P.apply inst2 subprob



composeProcessor :: S.StdProcessor (Compose P.AnyProcessor P.AnyProcessor)
composeProcessor = S.StdProcessor Compose

composeDynamic :: (P.Processor p1, P.Processor p2) => Bool -> P.InstanceOf p1 -> P.InstanceOf p2 -> P.InstanceOf (S.StdProcessor (Compose p1 p2))
composeDynamic relative p1 p2 = S.StdProcessor Compose `S.withArgs` (Nothing :+: relative :+: p1 :+: p2)

composeStatic :: (P.Processor p1, P.Processor p2) => PartitionFn -> Bool -> P.InstanceOf p1 -> P.InstanceOf p2 -> P.InstanceOf (S.StdProcessor (Compose p1 p2))
composeStatic split relative p1 p2 = S.StdProcessor Compose `S.withArgs` (Just split :+: relative :+: p1 :+: p2)