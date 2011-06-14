{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE TypeSynonymInstances #-}
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
    , processor
    , strategy
    , processorFromInstance
    , customInstance)
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

class IsDescription d arg | d -> arg where
  toDescription :: d -> Description arg
  
instance IsDescription String A.Unit where
  toDescription name = Description { as = name, args = A.Unit, descr = [] }
  

instance IsDescription (Description arg) arg where
  toDescription = id


processor :: IsDescription d arg => 
                   d -> (forall m. P.SolverM m => A.Domains arg -> Problem -> m res) -> (CustomProcessor arg res)
processor d f = S.StdProcessor CP {description = toDescription d, code = f }
                               
strategy :: IsDescription d arg => 
               (forall m. P.SolverM m => A.Domains arg -> Problem -> m res) -> d -> (CustomProcessor arg res)
strategy f d = processor d f               

processorFromInstance :: (IsDescription d arg, P.Processor proc) => 
             d -> (A.Domains arg -> P.InstanceOf proc) -> (CustomProcessor arg (P.ProofOf proc))
processorFromInstance d mkInst = processor d (P.solve . mkInst) 


customInstance :: P.ComplexityProof res => String -> (forall m. P.SolverM m => Problem -> m res) -> P.InstanceOf (CustomProcessor A.Unit res)
customInstance name f = processor d (const f) `S.withArgs` ()
  where d = Description { as = name, descr = [], args = A.unit }
