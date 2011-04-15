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

module Tct.Method.Combine where

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
import Termlib.Rule (Rule)
import Termlib.Problem (strictTrs, weakTrs, relation, Relation(..), Problem, startTerms, StartTerms (..))

-- static partitioning

data PartitionFn = Random deriving (Show, Typeable, Ord, Enum, Eq, Bounded)

staticAssign :: PartitionFn -> Problem -> (p1, p2) -> (Problem, Problem)
staticAssign Random problem _ = (mkProb r_1 r_2, mkProb r_2 r_1)
    where r = strictTrs problem
          s = weakTrs problem
          (r_1, r_2) = halve r
          mkProb strict weak = problem {relation = mkRel (Trs strict) (Trs weak `union` s) }
          mkRel = case relation problem of DP _ _ -> DP; _ -> Relative
          halve (Trs rs) = partitionEithers [ if b then Left rule else Right rule | (b,rule) <- zip (intersperse True (repeat False)) rs]

-- Waldmann Conditions

-- MA:TODO: think about applicable predicate
wcAppliesTo :: Problem -> (Bool, String)
wcAppliesTo prob = (not isRcProblem && not isDpProblem && weakNoneSizeIncreasing, reason)
  where isDpProblem            = case relation prob of {DP{} -> True; _ -> False}
        isRcProblem            = case startTerms prob of {TermAlgebra{} -> False; _ -> True}
        weakNoneSizeIncreasing = Trs.isEmpty weak || Trs.isNonSizeIncreasing weak
          where weak = weakTrs prob
        reason | isDpProblem = "the relative processor is not implemented for DP problems" 
               | isRcProblem = "the relative processor is not applicable to runtime complexity problems"
               | otherwise   = "the weak TRS is size-increasing"                   

-- Processor

data Combine p1 p2 = Combine

data CombineProof p1 p2 = StaticPartitioned PartitionFn (P.Proof p1) (P.Proof p2)
                        | DynamicPartitioned Bool (P.PartialProof (P.ProofOf p1)) (P.Proof p2)
                        | RelativeEmpty 

removedRules :: CombineProof p1 p2 -> [Rule]
removedRules (DynamicPartitioned _ rp _) = P.ppRemovable rp
removedRules _= []
             
instance (P.Processor p1, ComplexityProof (P.ProofOf p1) 
         , P.Processor p2, ComplexityProof (P.ProofOf p2))
    => PrettyPrintable (CombineProof p1 p2) where
    pprint RelativeEmpty = paragraph "The strict component is empty."
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
        $+$ pprint subproof


ub :: Answerable a => a -> Complexity
ub = upperBound . certificate . answer

instance (Answerable (P.ProofOf p1), Answerable (P.ProofOf p2)) => Answerable (CombineProof p1 p2) where
    answer RelativeEmpty = CertAnswer $ certified (constant, constant)
    answer (StaticPartitioned _ p1 p2) | success   = CertAnswer $ certified (unknown, ub p1 `add` ub p2)
                                       | otherwise = MaybeAnswer
        where success = succeeded p1 && succeeded p2
    answer (DynamicPartitioned relApplied  prel psub) | succeeded psub = CertAnswer $ certified (unknown, res)
                                                      | otherwise = MaybeAnswer
        where res | not relApplied = ub prel `add` ub psub
                  | otherwise    = combine (upperBound $ P.certificate prel) (upperBound $ P.certificate psub)
              r       = Trs.fromRules $ P.ppRemovable prel
              s       = strictTrs $ P.inputProblem psub
              sizeIncreasingR = Trs.isSizeIncreasing r
              sizeIncreasingS = Trs.isSizeIncreasing s
              combine ubRModS ubS | not sizeIncreasingS
                                    && not sizeIncreasingR  = ubRModS `mult` ubS
                                  | not sizeIncreasingS    = ubRModS `mult` (ubS `compose` (poly (Just 1) `add` ubRModS))
                                  | otherwise            = ubRModS `mult` (ubS `iter` ubRModS)

instance (Verifiable (P.ProofOf p1), Verifiable (P.ProofOf p2)) => Verifiable (CombineProof p1 p2) where
    -- MA:TODO verify splitting function
    verify _ (StaticPartitioned _ p1 p2) = P.verify (P.inputProblem p1) (P.result p1)
                                           `P.andVerify` P.verify (P.inputProblem p2) (P.result p2)
    verify _ (DynamicPartitioned _ _ psub) = P.verify (P.inputProblem psub) (P.result psub)
    verify _ _                             = P.verifyOK


instance (P.Processor p1, P.Processor p2) => S.Processor (Combine p1 p2) where
    type S.ArgumentsOf (Combine p1 p2) = Arg (EnumOf PartitionFn) :+: Arg Bool :+: Arg Bool :+: Arg (Proc p1) :+: Arg (Proc p2)
    type S.ProofOf (Combine p1 p2)     = CombineProof p1 p2

    name Combine        = "combine"

    instanceName inst   = (S.name $ S.processor inst) ++ if isStatic then "" else " (dynamic)"
        where _ :+: isStatic :+: _ :+: _ :+: _ = S.processorArgs inst
    description Combine = [ unlines [ "Given a TRS R, 'combine p_1 ... p_n' partitions R into TRSs R_1, ..., R_n" 
                                    , "and applies each processor p_i on the (relative) problem R_i modulo R\\R_i,"
                                    , "i.e., processor p_i is used to measure the number of R_i steps in R-derivations."]
                          , "The (asymptotic) upper-bound for the complexity of R is the worst upper-bound of the R_i's." ]
    arguments Combine   = opt { A.name = "split" 
                              , A.defaultValue = Random
                              , A.description = unlines ["This flag defines how the input TRS R is partitioned into the TRSs (R_1, R_2) if the option '-static' is set."
                                                        , "Currently only 'random' is implemented, which randomly partitions R into two equally sized TRSs."]}
                          :+: opt { A.name = "static"
                                  , A.defaultValue = False
                                  , A.description = unlines [ "If this argument is set then the input TRS R is partitioned into TRSs (R_1,R_2) according to the flag 'split'."
                                                            , "Otherwise the first given processor selects the TRS R_1" ] }
                          :+: opt { A.name = "relative"
                                  , A.defaultValue = False
                                  , A.description = unlines [ "This flag specifies how the second component R_2 is handled by the second given processor 'p2'"
                                                            , "If this flag is set, and one of the following criteria applies, processor 'p2' is used to estimate the complexity of R_2."
                                                            , "Otherwise, the subproblem is R_2 modulo R_1."
                                                            , "Criteria (aka Waldmann's relative criteria): (TODO ADAPT!)"
                                                            , "Let R = R_1 \\cup R_2"
                                                            , "  1) if R_1 and R_2 are non-size-increasing then dc(n, ->_R) = O(dc(n, ->R_1/R_2) * dc(n, ->_R_1/R_2))"
                                                            , "  2) if R_2 is non-size-increasing then dc(n, ->_R) = O(dc(n, ->_R/S) * dc(n, ->_S))"
                                                            , "  3) if R_2 is non-size-increasing then dc(n, ->_R) = O(dc(n, ->_R/S) * dc(n, ->_S))"
                                                            , "Above criteria applie only for derivational complexity"] }
                          :+: arg { A.name = "Subprocessor 1"
                                  , A.description = unlines ["The Processor to estimate the complexity of R_1 modulo R_2"]}
                          :+: arg { A.name = "Subprocessor 2"
                                  , A.description = unlines ["The Processor to estimate the complexity of R_2 modulo R_1, or respectively R_2"] }

    solve inst prob | Trs.isEmpty (strictTrs prob) = return RelativeEmpty 
                    | static    = solveStatic
                    | otherwise = solveDynamic
        where split :+: static :+: relative :+: inst1 :+: inst2 = S.processorArgs inst
              (relativeApplicable, _) =  wcAppliesTo prob
              solveStatic = let (p1,p2) = staticAssign split prob (inst1, inst2)
                            in liftM2 (StaticPartitioned split) (P.apply inst1 p1) (P.apply inst2 p2)
              solveDynamic = do res <- P.solvePartial inst1 prob
                                let removed = Trs.fromRules (P.ppRemovable res)
                                    relApplied = relative && relativeApplicable
                                    subprob = case relApplied of 
                                                True  -> prob { startTerms = TermAlgebra
                                                             , relation = case relation prob of 
                                                                            Standard strict      -> Standard $ strict \\ removed
                                                                            Relative strict weak -> Relative (strict \\ removed) weak
                                                                            DP       _      _    -> error "Relative Rule Removal inapplicable for DP problems" }
                                                          
                                                False -> prob { relation = case relation prob of 
                                                                            Standard strict      -> Relative (strict \\ removed) removed
                                                                            Relative strict weak -> Relative (strict \\ removed) (weak `union` removed)
                                                                            DP       strict weak -> DP (strict \\ removed) (weak `union` removed) }
                                DynamicPartitioned relApplied res `liftM` P.apply inst2 subprob



combineProcessor :: S.StdProcessor (Combine P.AnyProcessor P.AnyProcessor)
combineProcessor = S.StdProcessor Combine

type CombineInstance p1 p2 = P.InstanceOf (S.StdProcessor (Combine p1 p2))

combineDynamic :: (P.Processor p1, P.Processor p2) => Bool -> P.InstanceOf p1 -> P.InstanceOf p2 -> CombineInstance p1 p2
combineDynamic relative p1 p2 = Combine `S.withArgs` (Random :+: False :+: relative :+: p1 :+: p2)

combineStatic :: (P.Processor p1, P.Processor p2) => Bool -> P.InstanceOf p1 -> P.InstanceOf p2 -> CombineInstance p1 p2
combineStatic relative p1 p2 = Combine `S.withArgs` (Random :+: True :+: relative :+: p1 :+: p2)