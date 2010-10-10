{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
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
    ( CustomProcessor (..)
    , customProcessor
    , proc
    , pure)
where

import qualified Tct.Processor.Standard as S
import qualified Tct.Processor as P
import qualified Tct.Processor.Args as A
import Tct.Proof
import Termlib.Problem (Problem)

data CustomProcessor arg res = CustomProcessor { as  :: String
                                               , description :: [String]
                                               , args :: arg
                                               , code :: forall m. P.SolverM m => A.Domains arg -> Problem -> m res}

--------------------------------------------------------------------------------
-- processor instance

instance (ComplexityProof res) => S.Processor (CustomProcessor arg res) where
  type S.ProofOf (CustomProcessor arg res)     = res
  type S.ArgumentsOf (CustomProcessor arg res) = arg
  name        = as
  description = description
  arguments   = args
  solve inst prob = (code p) ags prob
      where p = S.processor inst
            ags = S.processorArgs inst

--------------------------------------------------------------------------------
-- convenience

customProcessor :: (CustomProcessor arg p)
customProcessor = CustomProcessor { as = "unknown"
                                  , code = error "code must be specified when adding custom processor"
                                  , args = error "args must be specified when adding custom processor"
                                  , description = [] }

proc :: (P.SolverM m, P.Processor p) => (args -> P.InstanceOf p) -> args-> Problem -> m (P.ProofOf p)
proc p aa prob = P.solve (p aa) prob

pure :: (P.SolverM m, ComplexityProof res) => (args -> Problem -> res) -> (args -> Problem -> m res)
pure f aa prob = return $ f aa prob


-- withArgs :: ComplexityProof p => CustomProcessor arg p -> A.Domains arg -> P.InstanceOf (S.StdProcessor (CustomProcessor arg p))
-- p `withArgs` a = p `S.withArgs` a