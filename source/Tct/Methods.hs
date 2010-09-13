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
    , bestProcessor
    , boundsProcessor
    , combineProcessor
    , epostarProcessor
    , fastestProcessor
    , iteProcessor
    , lmpoProcessor
    , matrixProcessor
    , popstarProcessor
    , sequentiallyProcessor
    , successProcessor
    , timeoutProcessor
 
    -- * Processors
    , best
    , bounds
    , combine
    , epostar
    , fail
    , fastest
    , ite
    , matrix
    , popstar
    , sequentially
    , success
    , timeout

    -- ** Argument Construction
    , NaturalMIKind (..)
    , Size (..)
    , nat
    , Enrichment (..)
    , InitialAutomaton (..)

    -- ** The Default Processor Used by TCT
    , defaultProcessor
    )
where
import Prelude()

import Tct.Method.Combinator
import Tct.Method.PopStar
import Tct.Method.EpoStar
import Tct.Method.Combine
import Tct.Method.Bounds
import Tct.Method.Matrix.NaturalMI
import Qlogic.NatSat (Size (..))
import Tct.Processor.Args.Instances

import Tct.Processor.Timeout
import Tct.Processor (none, (<|>), AnyProcessor)

defaultProcessor :: AnyProcessor
defaultProcessor = timeoutProcessor defaultProcessor
                   <|> failProcessor 
                   <|> successProcessor
                   <|> iteProcessor defaultProcessor defaultProcessor defaultProcessor
                   <|> bestProcessor
                   <|> fastestProcessor
                   <|> sequentiallyProcessor
                   <|> lmpoProcessor
                   <|> popstarProcessor
                   <|> epostarProcessor
                   <|> boundsProcessor
                   <|> matrixProcessor
                   <|> combineProcessor
                   <|> none