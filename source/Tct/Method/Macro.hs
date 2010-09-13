{-# LANGUAGE TypeFamilies #-}
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

module Tct.Method.Macro where

import qualified Tct.Processor as P
import qualified Tct.Processor.Args as A
import Tct.Processor.Standard (mkParseProcessor)
data Custom arg p = Custom { as  :: String
                           , description :: [String]
                           , args :: arg
                           --                         , argDescription :: String
                           , fn :: A.Domains arg -> P.InstanceOf p }

instance (P.Processor p) => P.Processor (Custom arg p) where
  type P.ProofOf (Custom arg p) = P.ProofOf p
  data P.InstanceOf (Custom arg p) = Inst (P.InstanceOf p)
  name                  = as
  instanceName (Inst p) = P.instanceName p
  description           = description
  solve_ (Inst p)       = P.solve p


instance (A.ParsableArguments arg, P.Processor p) => P.ParsableProcessor (Custom arg p) where
    synopsis p = as p ++ " " ++ A.synopsis (args p)
    parseProcessor_ p = do aa <- mkParseProcessor (as p) (args p)
                           return $ Inst $ (fn p) aa

custom :: Custom arg p
custom = Custom { as = "unknown"
                , fn = error "fn must be specified when adding custom processor"
                , args = error "args must be specified when adding custom processor"
                , description = [] }