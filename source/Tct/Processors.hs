{-# LINE 1 "/home/zini/tct/tct/source/Tct/_Processors_.hs" #-}
# 1 "/home/zini/tct/tct/source/Tct/_Processors_.hs"
# 1 "<built-in>"
# 1 "<command-line>"
# 1 "/home/zini/tct/tct/source/Tct/_Processors_.hs"
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

{-# LANGUAGE CPP #-}
{-# OPTIONS_GHC -w #-}
module Tct.Processors where

import Prelude hiding (fail, uncurry)
import qualified Tct.Processor as P
import qualified Tct.Processor.Standard as S

# 1 "/home/zini/tct/tct/source/Tct/_Processors_Imports_.hs" 1
-- generated: Sat Dec 24 22:49:26 JST 2011
import qualified Tct.Processor as P
import qualified Tct.Processor.Standard as S
import qualified Tct.Method.Predicates as Preds
import Tct.Processor.Timeout (timeoutProcessor)
import Tct.Method.PopStar (popstarProcessor)
import Tct.Method.PopStar (ppopstarProcessor)
import Tct.Method.PopStar (lmpoProcessor)
import Tct.Method.Bounds (boundsProcessor)
import Tct.Method.Combinator (failProcessor)
import Tct.Method.Combinator (successProcessor)
import Tct.Method.Combinator (emptyProcessor)
import Tct.Method.Combinator (openProcessor)
import Tct.Method.Combinator (iteProcessor)
import Tct.Method.Combinator (bestProcessor)
import Tct.Method.Combinator (fastestProcessor)
import Tct.Method.Combinator (sequentiallyProcessor)
import Tct.Method.EpoStar (epostarProcessor)
import Tct.Method.Matrix.NaturalMI (matrixProcessor)
import Tct.Method.Matrix.ArcticMI (arcticProcessor)
import Tct.Method.Poly.NaturalPI (polyProcessor)
import Tct.Method.InnermostRuleRemoval (irrProcessor)
import Tct.Method.ComposeRC (composeRCProcessor)
import Tct.Method.Weightgap (weightgapProcessor)
import Tct.Method.Compose (composeProcessor)
import Tct.Method.DP.DependencyPairs (dependencyPairsProcessor)
import Tct.Method.DP.Simplification (removeTailProcessor)
import Tct.Method.DP.Simplification (simpDPRHSProcessor)
import Tct.Method.DP.Simplification (simpKPProcessor)
import Tct.Method.DP.UsableRules (usableRulesProcessor)
import Tct.Method.DP.PathAnalysis (pathAnalysisProcessor)
import Tct.Method.Uncurry (uncurryProcessor)
# 49 "/home/zini/tct/tct/source/Tct/_Processors_.hs" 2

-- * Complexity Processors

# 1 "/home/zini/tct/tct/source/Tct/_Processors_Defs_.hs" 1
-- generated: Sat Dec 24 22:49:26 JST 2011
timeout = timeoutProcessor

popstar = popstarProcessor

ppopstar = ppopstarProcessor

lmpo = lmpoProcessor

bounds = boundsProcessor

fail = failProcessor

success = successProcessor

empty = emptyProcessor

open = openProcessor

ite = iteProcessor

best = bestProcessor

fastest = fastestProcessor

sequentially = sequentiallyProcessor

epostar = epostarProcessor

matrix = matrixProcessor

arctic = arcticProcessor

poly = polyProcessor

# 52 "/home/zini/tct/tct/source/Tct/_Processors_.hs" 2

-- * Complexity Transformations

# 1 "/home/zini/tct/tct/source/Tct/_Transformations_Defs_.hs" 1
-- generated: Sat Dec 24 22:49:26 JST 2011
irr = irrProcessor

composeRC = composeRCProcessor

weightgap = weightgapProcessor

compose = composeProcessor

dependencyPairs = dependencyPairsProcessor

removeTail = removeTailProcessor

simpDPRHS = simpDPRHSProcessor

simpKP = simpKPProcessor

usableRules = usableRulesProcessor

pathAnalysis = pathAnalysisProcessor

uncurry = uncurryProcessor

# 55 "/home/zini/tct/tct/source/Tct/_Processors_.hs" 2

-- * Built-in Processor

# 1 "/home/zini/tct/tct/source/Tct/_BuiltIn_.hs" 1
builtInProcessors :: P.AnyProcessor
builtInProcessors = 
    P.SomeProcessor timeout 
    P.<|>
    P.SomeProcessor popstar 
    P.<|>
    P.SomeProcessor ppopstar 
    P.<|>
    P.SomeProcessor lmpo 
    P.<|>
    P.SomeProcessor bounds 
    P.<|>
    P.SomeProcessor fail 
    P.<|>
    P.SomeProcessor success 
    P.<|>
    P.SomeProcessor empty 
    P.<|>
    P.SomeProcessor open 
    P.<|>
    P.SomeProcessor ite 
    P.<|>
    P.SomeProcessor best 
    P.<|>
    P.SomeProcessor fastest 
    P.<|>
    P.SomeProcessor sequentially 
    P.<|>
    P.SomeProcessor epostar 
    P.<|>
    P.SomeProcessor matrix 
    P.<|>
    P.SomeProcessor arctic 
    P.<|>
    P.SomeProcessor poly 
    P.<|>
    P.SomeProcessor (S.StdProcessor irr)
    P.<|>
    P.SomeProcessor (S.StdProcessor composeRC)
    P.<|>
    P.SomeProcessor (S.StdProcessor weightgap)
    P.<|>
    P.SomeProcessor (S.StdProcessor compose)
    P.<|>
    P.SomeProcessor (S.StdProcessor dependencyPairs)
    P.<|>
    P.SomeProcessor (S.StdProcessor removeTail)
    P.<|>
    P.SomeProcessor (S.StdProcessor simpDPRHS)
    P.<|>
    P.SomeProcessor (S.StdProcessor simpKP)
    P.<|>
    P.SomeProcessor (S.StdProcessor usableRules)
    P.<|>
    P.SomeProcessor (S.StdProcessor pathAnalysis)
    P.<|>
    P.SomeProcessor (S.StdProcessor uncurry)
    P.<|>
    foldr (P.<|>) P.none Preds.predicateProcessors
# 58 "/home/zini/tct/tct/source/Tct/_Processors_.hs" 2
