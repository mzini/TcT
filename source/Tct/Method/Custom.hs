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
    , localProcessor
    , processor
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


         
type CustomProcessor arg p = S.StdProcessor (CP arg p)

customProcessor :: (forall m. P.SolverM m => A.Domains arg -> Problem -> m res) -> (Description arg) -> (CustomProcessor arg res)
customProcessor f d = S.StdProcessor CP {description = d, code = f }


               -- local :: P.ComplexityProof res =>
               --          String -> t -> P.InstanceOf (S.StdProcessor (CP A.Unit res))

localProcessor :: P.ComplexityProof res => String -> (forall m. P.SolverM m => Problem -> m res) -> P.InstanceOf (CustomProcessor A.Unit res)
localProcessor name f = S.StdProcessor (CP  d (\ () -> f)) `S.withArgs` ()
  where d = Description { as = name, descr = [], args = A.unit }
                               
processor :: P.Processor proc => (A.Domains arg -> P.InstanceOf proc) -> (Description arg) -> (CustomProcessor arg (P.ProofOf proc))
processor mkInst = customProcessor (P.solve . mkInst) 
--------------------------------------------------------------------------------
-- convenience

proc :: (P.SolverM m, P.Processor p) => (args -> P.InstanceOf p) -> args-> Problem -> m (P.ProofOf p)
proc p aa prob = P.solve (p aa) prob

pure :: (P.SolverM m, P.ComplexityProof res) => (args -> Problem -> res) -> (args -> Problem -> m res)
pure f aa prob = return $ f aa prob