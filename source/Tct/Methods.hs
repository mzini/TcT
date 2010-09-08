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

module Tct.Methods 
    (  -- *  Parsable Processors
     failProcessor
    , successProcessor
    , iteProcessor
    , bestProcessor
    , fastestProcessor
    , sequentiallyProcessor
    , combineProcessor
    , matrixProcessor
    , boundsProcessor
    , popstarProcessor
    , lmpoProcessor
      
    -- * Processors
    , fail
    , success
    , ite
    , best
    , fastest
    , sequentially
    , combine
    , matrix
    , bounds
    , popstar

    -- ** Argument Construction
    , NaturalMIKind (..)
    , Size (..)
    , nat
    , Enrichment (..)
    , InitialAutomaton (..)
    )
where
import Prelude()

import Tct.Method.Combinator
import Tct.Method.PopStar
import Tct.Method.Combine
import Tct.Method.Bounds
import Tct.Method.Matrix.NaturalMI
import Qlogic.NatSat (Size (..))
import Tct.Processor.Args.Instances