{-# LANGUAGE Rank2Types #-}
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

{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE PolymorphicComponents #-}

module Tct.Method.Custom 
    ( Description (..)
    , CustomProcessor
    , customProcessor
    , proc
    , pure)
where

import qualified Tct.Processor.Standard as S
import qualified Tct.Processor as P
import qualified Tct.Processor.Args as A
import Termlib.Problem (Problem)

data Description arg = Description { as    :: String
                                   , descr :: [String]
                                   , args  :: arg}

data CP arg res = CP { description :: Description arg
                     , code :: forall m. P.SolverM m => A.Domains arg -> Problem -> m res} 

--------------------------------------------------------------------------------
-- processor instance

instance (P.ComplexityProof res) => S.Processor (CP arg res) where
  type S.ProofOf (CP arg res)     = res
  type S.ArgumentsOf (CP arg res) = arg
  name        = as . description
  description = descr . description
  arguments   = args . description
  solve inst prob = (code p) ags prob
      where p = S.processor inst
            ags = S.processorArgs inst

--------------------------------------------------------------------------------
-- convenience

-- customProcessor fn Description { as = "foo"
--                                , descr = ["bar"]}
         
type CustomProcessor arg p = S.StdProcessor (CP arg p)

customProcessor :: (forall m. P.SolverM m => A.Domains arg -> Problem -> m res) -> (Description arg) -> (CustomProcessor arg res)
customProcessor f descr = S.StdProcessor CP {description = descr , code       = f }

proc :: (P.SolverM m, P.Processor p) => (args -> P.InstanceOf p) -> args-> Problem -> m (P.ProofOf p)
proc p aa prob = P.solve (p aa) prob

pure :: (P.SolverM m, P.ComplexityProof res) => (args -> Problem -> res) -> (args -> Problem -> m res)
pure f aa prob = return $ f aa prob


-- withArgs :: ComplexityProof p => CustomProcessor arg p -> A.Domains arg -> P.InstanceOf (S.StdProcessor (CustomProcessor arg p))
-- p `withArgs` a = p `S.withArgs` a