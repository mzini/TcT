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
import Control.Monad (liftM, forM)
import Data.Either (partitionEithers)
import Text.PrettyPrint.HughesPJ

import qualified Tct.Processor as P
import Tct.Processor.PPrint
import qualified Tct.Processor.Standard as S
import Tct.Processor.Args
import qualified Tct.Processor.Args as A
import Tct.Processor.Args.Instances
import Tct.Certificate
import Tct.Proof
import Termlib.Utils (PrettyPrintable (..), paragraph)
import Termlib.Trs (Trs(..), rules, union)
import Termlib.Problem (strictTrs, weakTrs, relation, Relation(..), Problem)


data PartitionFn = Random deriving (Show, Typeable, Ord, Enum, Eq, Bounded)


assign :: PartitionFn -> [a] -> Problem -> [(a, Problem)]
assign Random processors problem = [(proc, problem {relation = mkrel mask}) | (proc, mask) <- take l (zip processors masks)]
    where mkrel mask = mkprob (Trs s') (w `union` Trs w')
              where (s', w') = partitionEithers [if b then Left rule else Right rule | (b, rule) <- zip mask $ rules s]
          mkprob = case relation problem of DP _ _ -> DP; _ -> Relative
          masks = msks fstMask
              where msks msk = msk : (msks (False : msk))
                    fstMask | l == 0    =  []
                            | otherwise = cycle $ True : (replicate (l - 1) False)
          s = strictTrs problem
          w = weakTrs problem
          l = length $ zip processors $ rules s


data Combine p = Combine

data CombineProof p = CombineProof PartitionFn [P.Proof p]

instance (P.Processor p, ComplexityProof (P.ProofOf p)) => PrettyPrintable (CombineProof p) where
    pprint (CombineProof split ps) = paragraph (unlines [ "We have partition the input TRS R into TRSs R_1, ...,R_" ++ (show n) ++ " as depicted below using the function "
                                                        , "'" ++ show split ++ "'" 
                                                        , "and apply the i-th given subprocessor on the relative problem R_i modulo R\\R_i."])
                                     $+$ (if success then empty else text "Unfortunately one of the subprocessors failed.")
                                     $+$ text ""
                                     $+$ overview (enumeration' ps)
                                     $+$ text ""
                                     $+$ details (enumeration' ps)
        where n = length ps
              success = all succeeded ps

--              probname i = text $ "R_" ++ show i ++ " modulo R\\R_" ++ show i

instance Answerable (P.ProofOf p) => Answerable (CombineProof p) where
    answer (CombineProof _ ps) | allcerts  = CertAnswer $ certified (unknown, ub [upperBound (certificate p) | p <- ps])
                               | otherwise = MaybeAnswer
        where ub []     = poly $ Just 0
              ub (p':ps') = foldl add p' ps'
              allcerts = all (succeeded . answer) $ ps

instance (P.Processor p, [P.InstanceOf p] ~ Domain [(S.StdProcessor p)]) => S.Processor (Combine p) where
    type S.ArgumentsOf (Combine p) = Arg (EnumOf PartitionFn) :+: Arg [S.StdProcessor p]
    type S.ProofOf (Combine p)     = CombineProof p

    name Combine        = "combine"

    instanceName inst   = (S.name $ S.processor inst) ++ " with splitting function '" ++ show split ++ "'"
        where split = case S.processorArgs inst of s :+: _ -> s
    description Combine = [ unlines [ "Given a TRS R, 'combine p_1 ... p_n' partitions R into TRSs R_1, ..., R_n" 
                                    , "and applies each processor p_i on the (relative) problem R_i modulo R\\R_i,"
                                    , "i.e., processor p_i is used to measure the number of R_i steps in R-derivations."]
                          , "The (asymptotic) upper-bound for the complexity of R is the worst upper-bound of the R_i's." ]
    arguments Combine   = opt { A.name = "split" 
                              , A.defaultValue = Random
                              , A.description = unlines ["This flag defines how the input TRS R is partitioned into the TRSs R_1, ..., R_n."
                                                        , "Currently only 'random' is implemented, which randomly partitions R into n equally sized TRSs."]}
                          :+: arg { A.name = "subprocessors"
                                  , A.description = unlines ["The list of processors used to handle the (relative) problem R_i modulo R\\R_i."]}

    solve inst prob = CombineProof split `liftM` (forM assigned $ \ (proc,prob') -> P.apply proc prob') -- TODO sequentially ! 
        where split :+: insts = S.processorArgs inst
              assigned = assign split insts prob
combineProcessor :: S.StdProcessor (Combine P.AnyProcessor)
combineProcessor = S.StdProcessor Combine


combine :: (P.Processor p) => [P.InstanceOf p] -> P.InstanceOf (S.StdProcessor (Combine p))
combine ps = Combine `S.withArgs` (Random :+: ps)