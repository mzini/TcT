{-# LANGUAGE NoMonomorphismRestriction #-}
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

{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeOperators #-}

module Tct.Methods 
    (  

    -- * Processors
    -- ** Direct Processors
      arctic
    , bounds
    , empty
    , epostar
    , fail
    , matrix
    , popstar
    , success


    -- ** Processor Combinators
    , before
    , best
    , composeDynamic
    , composeStatic
    , fastest
    , ite
    , orBetter
    , orFaster
    , sequentially
    , solveBy
    , timeout
    , upto
    , withArgs

    -- ** Transformations
    , irr
    , uncurry
    , pathAnalysis
    , dependencyPairs
    , usableRules
    , parallelSubgoals
    , sequentialSubgoals
    , strict      
    , nonstrict
    , (>>>)

    -- ** Predicates
    , isCollapsing
    , isConstructor
    , isDuplicating
    , isLeftLinear
    , isRightLinear
    , isWellFormed
    , trsPredicate
    , problemPredicate

    -- * Custom Processors
    , CustomProcessor
    , Description(..)
    , customProcessor
    , localProcessor 

    -- ** Arguments
    , Nat (..)
    , nat
    , Size (..)
    , EnumOf
    , Processor
    , NaturalMIKind (..)
    , Approximation(..)
    , Enrichment (..)
    , InitialAutomaton (..)
    , AssocArgument (..)      
    , Assoc 
    -- *** Argument Descriptions
    , Arg (..)
    , Unit    
    , (:+:)(..)
    , arg
    , optional
      
    -- *** Argument Description Constructors  
    , assocArg 
    , boolArg
    , enumArg
    , maybeArg
    , naturalArg
    , processorArg

    -- *  Parsable Processors
    , (<|>)
    , AnyProcessor
    , arcticProcessor
    , bestProcessor
    , boundsProcessor
    , composeProcessor
    , epostarProcessor
    , failProcessor
    , fastestProcessor
    , iteProcessor
    , lmpoProcessor
    , matrixProcessor
    , popstarProcessor
    , sequentiallyProcessor
    , successProcessor
    , timeoutProcessor

      -- ** The Built-In Processor Used by TCT
    , builtInProcessors
    , predicateProcessors

    -- ** Transformations
    , irrProcessor    
    , uncurryProcessor
    , dependencyPairsProcessor
    , pathAnalysisProcessor
    , usableRulesProcessor
    )
where
import Prelude hiding (fail, uncurry)

import Tct.Method.Combinator
import Tct.Method.PopStar
import Tct.Method.EpoStar
import Tct.Method.Compose
import Tct.Method.Bounds
import Tct.Method.Matrix.ArcticMI
import Tct.Method.Matrix.NaturalMI
import Tct.Method.Custom
import Tct.Method.Predicates
import Tct.Method.Uncurry
import Tct.Method.DP.UsableRules
import Tct.Method.DP.DependencyPairs
import Tct.Method.DP.PathAnalysis
import Tct.Method.DP.DependencyGraph hiding (strict, weak)
import Tct.Method.InnermostRuleRemoval
import Qlogic.NatSat (Size (..))
import qualified Tct.Processor as P
import Tct.Processor (solveBy)
import qualified Tct.Processor.Standard as S
import Tct.Processor.Standard (withArgs)
import Tct.Processor.Args
import Tct.Processor.Args.Instances
import Tct.Processor.Transformations -- (strict, nonstrict, parallelSubgoals, sequentialSubgoals, TransformationProcessor)
import Tct.Processor.Timeout
import Tct.Processor (none, (<|>), AnyProcessor)

builtInProcessors :: AnyProcessor
builtInProcessors = timeoutProcessor
                   <|> failProcessor 
                   <|> successProcessor
                   <|> iteProcessor
                   <|> irrProcessor
                   <|> bestProcessor
                   <|> fastestProcessor
                   <|> sequentiallyProcessor
                   <|> lmpoProcessor
                   <|> popstarProcessor
                   <|> epostarProcessor
                   <|> boundsProcessor
                   <|> uncurryProcessor
                   <|> usableRulesProcessor
                   <|> dependencyPairsProcessor
                   <|> pathAnalysisProcessor
                   <|> matrixProcessor
                   <|> arcticProcessor
                   <|> composeProcessor
                   <|> emptyProcessor
                   <|> foldr (<|>) none predicateProcessors

-- combinators

-- call :: (P.Processor p) => P.InstanceOf p -> P.InstanceOf P.SomeProcessor
-- call = P.someInstance

upto :: (Enum n, Ord n, P.ComplexityProof (P.ProofOf p), P.Processor p) =>
        (n -> P.InstanceOf p) -> (Bool :+: n :+: n) -> P.InstanceOf (S.StdProcessor (OneOf p))
upto prc (fast :+: l :+: u) | l > u     = fastest []
                            | fast      = fastest subs
                            | otherwise = sequentially subs
    where subs = [ prc i | i <- [l..u] ]

orFaster :: (P.Processor a, P.Processor b) => 
           P.InstanceOf a -> P.InstanceOf b -> P.InstanceOf (S.StdProcessor (OneOf P.SomeProcessor))
a `orFaster` b = fastest [P.someInstance a, P.someInstance b]

orBetter :: (P.Processor a, P.Processor b) => 
           P.InstanceOf a -> P.InstanceOf b -> P.InstanceOf (S.StdProcessor (OneOf P.SomeProcessor))
a `orBetter` b = best [P.someInstance a, P.someInstance b]

before :: (P.Processor a, P.Processor b) => 
           P.InstanceOf a -> P.InstanceOf b -> P.InstanceOf (S.StdProcessor (OneOf P.SomeProcessor))
a `before` b = sequentially [P.someInstance a, P.someInstance b]


-- transformation Combinators

(>>>) :: (Transformer t1, Transformer t2, P.Processor sub) => -- (Transformer t1, P.Processor sub, P.ComplexityProof (P.ProofOf (TransformationProcessor t1 sub)), Arguments (ArgumentsOf t1)
        (P.InstanceOf sub -> P.InstanceOf (TransformationProcessor t1 sub))
        -> (P.InstanceOf (TransformationProcessor t1 sub) -> P.InstanceOf (TransformationProcessor t2 (TransformationProcessor t1 sub)))
        -> P.InstanceOf sub -> P.InstanceOf (TransformationProcessor t2 (TransformationProcessor t1 sub))
tfn1 >>> tfn2 = \ sub -> (tfn2 (tfn1 sub))


-- can be used as follows :: foo = (strict . uncurry) >>> (nonstrict . irr)
