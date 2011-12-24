--------------------------------------------------------------------------------
-- | 
-- Module      :  Tct.Processors
-- Copyright   :  (c) Martin Avanzini <martin.avanzini@uibk.ac.at>, 
--                Georg Moser <georg.moser@uibk.ac.at>, 
--                Andreas Schnabl <andreas.schnabl@uibk.ac.at>,
-- License     :  LGPL (see COPYING)
--
-- Maintainer  :  Martin Avanzini <martin.avanzini@uibk.ac.at>
-- Stability   :  unstable
-- Portability :  unportable      
-- 
-- This module collects available /processors/ of TCT.
-- A processor 'p' is the TcT representation of a complexity techniques
-- that, given a complexity problem, constructs a complete proof for 
-- the problem. 
-- Processors are parameterised in some arguments that control the behaviour
-- of the processor, for instance, the matrix processor is parameterised 
-- in the dimension of the constructed matrix interpretation. 
-- Parameterised processors are called /processor instances/. 
--------------------------------------------------------------------------------      


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
      -- * Complexity Processors 
    ArcticMI.arcticProcessor
    , Bounds.boundsProcessor
    , Combinators.bestProcessor
    , Combinators.emptyProcessor
    , Combinators.failProcessor
    , Combinators.fastestProcessor
    , Combinators.iteProcessor
    , Combinators.sequentiallyProcessor
    , Combinators.successProcessor
    , EpoStar.epostarProcessor
    , NaturalMI.matrixProcessor
    , NaturalPI.polyProcessor
    , PopStar.lmpoProcessor
    , PopStar.popstarProcessor
    , Timeout.timeoutProcessor
      
    -- * Predicate Processors #predicates#
      -- | /Predicates/ are processors that return either 'Yes(?,?)' or 
      -- 'No'. In particular, these are useful as guards in conjunction 
      -- with the conditional processor 'iteProcessor'. 
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
      

    -- ** Transformations
    , Compose.composeProcessor
    , DP.dependencyPairsProcessor
    , DPSimp.removeTailProcessor
    , DPSimp.simpDPRHSProcessor
    , DPSimp.simpKPProcessor      
    , IRR.irrProcessor    
    , PathAnalysis.pathAnalysisProcessor
    , UR.usableRulesProcessor
    , Uncurry.uncurryProcessor
    , Weightgap.weightgapProcessor
      -- * Existential Quantification and Processor Collections
    , P.SomeProcessor
      -- | This is the existentially quantified type of a 
      -- processor. 
    , P.AnyProcessor
      -- | This type represents a collection of processors, 
      -- and is used for configuring TcT, c.f. module "Tct". 
    , (P.<|>)
      -- | Adds a processor to the processor collection.
    , (P.<++>)      
      -- | Append on 'P.AnyProcessor'.
    , P.toProcessorList
      -- | Extract the list of processors represented.
      
      -- * Processors Implemented in TcT      
    , builtInProcessors
      -- | This 'P.AnyProcessor' collects all processors implemented
      -- in TcT. A list of these processors can be extracted with
      -- 'P.toProcessorList'.
    , Predicates.predicateProcessors
      -- | This 'P.AnyProcessor' collects all predicates implemented
      -- in TcT, c.f., "Tct.Processors#predicates". A list of these processors can be extracted with
      -- 'P.toProcessorList'.
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
import qualified Tct.Processor.Standard as S
import qualified Tct.Processor.Timeout as Timeout

builtInProcessors :: P.AnyProcessor
builtInProcessors = Timeout.timeoutProcessor
                    P.<|> Combinators.failProcessor 
                    P.<|> Combinators.successProcessor
                    P.<|> Combinators.iteProcessor
                    P.<|> S.StdProcessor IRR.irrProcessor
                    P.<|> Combinators.bestProcessor
                    P.<|> Combinators.fastestProcessor
                    P.<|> Combinators.openProcessor                    
                    P.<|> Combinators.sequentiallyProcessor
                    P.<|> PopStar.lmpoProcessor
                    P.<|> PopStar.popstarProcessor
                    P.<|> PopStar.ppopstarProcessor
                    P.<|> EpoStar.epostarProcessor
                    P.<|> Bounds.boundsProcessor
                    P.<|> S.StdProcessor Uncurry.uncurryProcessor
                    P.<|> S.StdProcessor UR.usableRulesProcessor
                    P.<|> S.StdProcessor DPSimp.removeTailProcessor
                    P.<|> S.StdProcessor DPSimp.simpDPRHSProcessor                 
                    P.<|> S.StdProcessor DPSimp.simpKPProcessor                    
                    P.<|> S.StdProcessor DP.dependencyPairsProcessor
                    P.<|> S.StdProcessor PathAnalysis.pathAnalysisProcessor
                    P.<|> NaturalMI.matrixProcessor
                    P.<|> NaturalPI.polyProcessor
                    P.<|> ArcticMI.arcticProcessor
                    P.<|> S.StdProcessor Weightgap.weightgapProcessor
                    P.<|> S.StdProcessor Compose.composeProcessor
                    P.<|> S.StdProcessor ComposeRC.composeRCProcessor
                    P.<|> Combinators.emptyProcessor
                    P.<|> foldr (P.<|>) P.none Predicates.predicateProcessors
