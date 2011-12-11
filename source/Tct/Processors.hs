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
module Tct.Processors
    ( 
    -- *  Parsable Processors
    (P.<|>)
    , (P.<++>)
    , P.none
    , P.AnyProcessor
    , ArcticMI.arcticProcessor
    , Combinators.bestProcessor
    , Bounds.boundsProcessor
    , Combinators.failProcessor
    , Combinators.fastestProcessor
    , Combinators.iteProcessor
    , Combinators.emptyProcessor
    , Compose.composeProcessor
    , EpoStar.epostarProcessor
    , PopStar.lmpoProcessor
    , NaturalMI.matrixProcessor
    , NaturalPI.polyProcessor
    , PopStar.popstarProcessor
    , Combinators.sequentiallyProcessor
    , Combinators.successProcessor
    , Timeout.timeoutProcessor
    -- ** Predicates
    , Predicates.isCollapsingProcessor
    , Predicates.isConstructorProcessor
    , Predicates.isDuplicatingProcessor
    , Predicates.isLeftLinearProcessor
    , Predicates.isRightLinearProcessor
    , Predicates.isWellFormedProcessor
    , Predicates.isFullProcessor
    , Predicates.isInnermostProcessor
    , Predicates.isOutermostProcessor
    , Predicates.isContextSensitiveProcessor
      
      -- ** The Built-In Processor Used by TCT
    , builtInProcessors
    , Predicates.predicateProcessors

    -- ** Transformations
    , IRR.irrProcessor    
    , Uncurry.uncurryProcessor
    , DP.dependencyPairsProcessor
    , PathAnalysis.pathAnalysisProcessor
    , UR.usableRulesProcessor
    , Weightgap.weightgapProcessor
    , DPSimp.removeTailProcessor
    , DPSimp.simpDPRHSProcessor
    , DPSimp.simpKPProcessor      
    ) where

import qualified Tct.Method.Combinator as Combinators
import qualified Tct.Method.PopStar as PopStar
import qualified Tct.Method.EpoStar as EpoStar
import qualified Tct.Method.Compose as Compose
import qualified Tct.Method.ComposeRC as ComposeRC
import qualified Tct.Method.Bounds as Bounds
import qualified Tct.Method.Matrix.ArcticMI as ArcticMI
import qualified Tct.Method.DP.Simplification as DPSimp
import qualified Tct.Method.Matrix.NaturalMI as NaturalMI
import qualified Tct.Method.Poly.NaturalPI as NaturalPI
import qualified Tct.Method.Predicates as Predicates
import qualified Tct.Method.Uncurry as Uncurry
import qualified Tct.Method.DP.UsableRules as UR
import qualified Tct.Method.DP.DependencyPairs as DP
import qualified Tct.Method.DP.PathAnalysis as PathAnalysis
import qualified Tct.Method.Weightgap as Weightgap
import qualified Tct.Method.InnermostRuleRemoval as IRR
import qualified Tct.Processor as P
import qualified Tct.Processor.Timeout as Timeout

builtInProcessors :: P.AnyProcessor
builtInProcessors = Timeout.timeoutProcessor
                    P.<|> Combinators.failProcessor 
                    P.<|> Combinators.successProcessor
                    P.<|> Combinators.iteProcessor
                    P.<|> IRR.irrProcessor
                    P.<|> Combinators.bestProcessor
                    P.<|> Combinators.fastestProcessor
                    P.<|> Combinators.sequentiallyProcessor
                    P.<|> PopStar.lmpoProcessor
                    P.<|> PopStar.popstarProcessor
                    P.<|> PopStar.ppopstarProcessor
                    P.<|> EpoStar.epostarProcessor
                    P.<|> Bounds.boundsProcessor
                    P.<|> Uncurry.uncurryProcessor
                    P.<|> UR.usableRulesProcessor
                    P.<|> DPSimp.removeTailProcessor
                    P.<|> DPSimp.simpDPRHSProcessor                 
                    P.<|> DP.dependencyPairsProcessor
                    P.<|> PathAnalysis.pathAnalysisProcessor
                    P.<|> NaturalMI.matrixProcessor
                    P.<|> NaturalPI.polyProcessor
                    P.<|> ArcticMI.arcticProcessor
                    P.<|> Weightgap.weightgapProcessor
                    P.<|> Compose.composeProcessor
                    P.<|> ComposeRC.composeRCProcessor
                    P.<|> Combinators.emptyProcessor
                    P.<|> foldr (P.<|>) P.none Predicates.predicateProcessors
