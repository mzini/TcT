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

{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleInstances #-}

module Tct.Method.DP.UsableRules where

import qualified Data.Set as Set
import Text.PrettyPrint.HughesPJ hiding (empty)

import qualified Termlib.FunctionSymbol as F
import qualified Termlib.Variable as V
import qualified Termlib.Problem as Prob
import qualified Termlib.Term as Term
import qualified Termlib.Rule as R
import Termlib.Rule (Rule (..))
import qualified Termlib.Trs as Trs
import Termlib.Trs (Trs(..))
import Termlib.Trs.PrettyPrint (pprintNamedTrs)
import Termlib.Utils hiding (block)
import Termlib.Utils as Utils

import qualified Tct.Processor.Transformations as T
import qualified Tct.Processor as P
import Tct.Processor.PPrint
import Tct.Method.DP.Utils 
import Tct.Method.DP.DependencyGraph


data RemoveLeaf = RemoveLeaf
data RemoveLeafProof = RLProof { removeds :: [Node] 
                               , graph    :: DependencyGraph Node
                               , signature :: F.Signature
                               , variables :: V.Variables}
                     | Error DPError
instance T.TransformationProof RemoveLeaf where
  answer = answerFromSubProof
  pprintProof _ (Error e) = pprint e
  pprintProof _ p         = text "We consider the dependency-graph"
                            $+$ text ""
                            pprint (graph p, sig, vars)
     where vars = variables p                              
           sig = signature p