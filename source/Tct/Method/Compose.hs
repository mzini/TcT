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

-- Waldmann/Hofbauer Conditions

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

data Compose p1 p2 = Compose

data ComposeProof p1 p2 = StaticPartitioned PartitionFn (P.Proof p1) (P.Proof p2)
                        | DynamicPartitioned Bool (P.PartialProof (P.ProofOf p1)) (P.Proof p2)
                        | NoRuleRemoved (P.PartialProof (P.ProofOf p1))
                        | RelativeEmpty 

removedRules :: ComposeProof p1 p2 -> [Rule]
removedRules (DynamicPartitioned _ rp _) = P.ppRemovable rp
removedRules _= []
             
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
                  | otherwise    = compose (upperBound $ P.certificate prel) (upperBound $ P.certificate psub)
              r       = Trs.fromRules $ P.ppRemovable prel
              s       = strictTrs $ P.inputProblem psub
              sizeIncreasingR = Trs.isSizeIncreasing r
              sizeIncreasingS = Trs.isSizeIncreasing s
              compose ubRModS ubS | not sizeIncreasingS
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
    type S.ArgumentsOf (Compose p1 p2) = Arg (EnumOf PartitionFn) :+: Arg Bool :+: Arg Bool :+: Arg (Proc p1) :+: Arg (Proc p2)
    type S.ProofOf (Compose p1 p2)     = ComposeProof p1 p2

    name Compose        = "compose"

    instanceName inst   = (S.name $ S.processor inst) ++ if isStatic then "" else " (dynamic)"
        where _ :+: isStatic :+: _ :+: _ :+: _ = S.processorArgs inst
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
    arguments Compose   = opt { A.name = "split" 
                              , A.defaultValue = Random
                              , A.description = unwords ["This flag defines how the input TRS R is partitioned into the TRSs (R_1,R_2) if the option 'static' is set."
                                                       , "Currently only 'Random' is implemented, which randomly partitions R into two equally sized TRSs."]}
                          :+: opt { A.name = "static"
                                  , A.defaultValue = False
                                  , A.description = unwords [ "If this argument is set then the input TRS R is partitioned into TRSs (R_1,R_2) according to the flag 'split'."
                                                            , "Otherwise the first given processor selects the TRS R_1." ] }
                          :+: opt { A.name = "relative"
                                  , A.defaultValue = False
                                  , A.description = unwords [ "This flag specifies how the second component R_2 is handled by the second given processor 'p2'."
                                                            , "If this flag is set, and one of the above criteria 1--3 applies, processor 'p2' is used to estimate the complexity of R_2."
                                                            , "Otherwise, the processor 'p2' is applied on the subproblem R_2 modulo R_1."] }
                          :+: arg { A.name = "Subprocessor 1"
                                  , A.description = unlines ["The Processor to estimate the complexity of R_1 modulo R_2."]}
                          :+: arg { A.name = "Subprocessor 2"
                                  , A.description = unlines ["The Processor to estimate the complexity of R_2 modulo R_1, or respectively R_2."] }

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
                                case null $ Trs.rules removed of 
                                  True  -> return $ NoRuleRemoved res
                                  False -> DynamicPartitioned relApplied res `liftM` P.apply inst2 subprob



composeProcessor :: S.StdProcessor (Compose P.AnyProcessor P.AnyProcessor)
composeProcessor = S.StdProcessor Compose

type ComposeInstance p1 p2 = P.InstanceOf (S.StdProcessor (Compose p1 p2))

composeDynamic :: (P.Processor p1, P.Processor p2) => Bool -> P.InstanceOf p1 -> P.InstanceOf p2 -> ComposeInstance p1 p2
composeDynamic relative p1 p2 = S.StdProcessor Compose `S.withArgs` (Random :+: False :+: relative :+: p1 :+: p2)

composeStatic :: (P.Processor p1, P.Processor p2) => Bool -> P.InstanceOf p1 -> P.InstanceOf p2 -> ComposeInstance p1 p2
composeStatic relative p1 p2 = S.StdProcessor Compose `S.withArgs` (Random :+: True :+: relative :+: p1 :+: p2)