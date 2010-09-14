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
    ( Custom (..)
    , custom
    , processor
    , pure)
where

import qualified Tct.Processor as P
import qualified Tct.Processor.Args as A
import Tct.Proof
import Termlib.Problem (Problem)
import Tct.Processor.Standard (mkParseProcessor)


data Custom arg res = Custom { as  :: String
                             , description :: [String]
                             , args :: arg
                             , code :: forall m. P.SolverM m => A.Domains arg -> Problem -> m res}

--------------------------------------------------------------------------------
-- processor instance

instance (ComplexityProof res) => P.Processor (Custom arg res) where
  type P.ProofOf    (Custom arg res) = res
  data P.InstanceOf (Custom arg res) = Inst (Custom arg res) (A.Domains arg)
  name                    = as
  instanceName (Inst p _) = as p
  description             = description
  solve_ (Inst p aa) prob = (code p) aa prob

instance (A.ParsableArguments arg, ComplexityProof res) => P.ParsableProcessor (Custom arg res) where
    synopsis p = as p ++ " " ++ A.synopsis (args p)
    parseProcessor_ p = do aa <- mkParseProcessor (as p) (args p)
                           return $ Inst p aa


--------------------------------------------------------------------------------
-- convenience

custom :: Custom arg p
custom = Custom { as = "unknown"
                , code = error "code must be specified when adding custom processor"
                , args = error "args must be specified when adding custom processor"
                , description = [] }

processor :: (P.SolverM m, P.Processor p) => (t -> P.InstanceOf p) -> t-> Problem -> m (P.ProofOf p)
processor p aa prob = P.solve (p aa) prob

pure :: (P.SolverM m, ComplexityProof res) => (t -> Problem -> res) -> (t -> Problem -> m res)
pure f aa prob = return $ f aa prob