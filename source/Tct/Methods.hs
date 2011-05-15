{-# LANGUAGE FlexibleInstances #-}
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
    -- ** Default Option
    P.defaultOptions 
    , DefaultMatrix (..)

    -- ** Direct Processors
    , arctic
    , bounds
    , empty
    , epostar
    , fail
    , matrix
    , popstarPS
    , lmpoPS
    , popstar
    , lmpo     
    , success


    -- ** Processor Combinators
    , before
    , best
    , Compose.composeDynamic
    , Compose.composeDP
    , Compose.composeRandom
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
    , thenApply
    , irr
    , uncurry
    , pathAnalysis
    , dependencyPairs
    , dependencyTuples
    , usableRules
    , weightgap
    , (>>>)
    , exhaustively
    , try

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
    , processor

    -- ** Arguments
    , Nat (..)
    , nat
    , Size (..)
    , EnumOf
    , Processor
    , NaturalMI.NaturalMIKind (..)
    , Weightgap.WgOn (..)
    , Compose.ComposeBound (..)
    , Compose.Partitioning (..)
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
    , ArcticMI.arcticProcessor
    , bestProcessor
    , boundsProcessor
    , Compose.composeProcessor
    , epostarProcessor
    , failProcessor
    , fastestProcessor
    , iteProcessor
    , lmpoProcessor
    , NaturalMI.matrixProcessor
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
    , Weightgap.weightgapProcessor
    )
where
import Prelude hiding (fail, uncurry)

import Tct.Method.Combinator
import Tct.Method.PopStar
import Tct.Method.EpoStar
import qualified Tct.Method.Compose as Compose
import Tct.Method.Bounds
import qualified Tct.Method.Matrix.ArcticMI as ArcticMI
import qualified Qlogic.ArcSat as ArcSat

import qualified Tct.Method.Matrix.NaturalMI as NaturalMI
import Tct.Method.Custom
import Tct.Method.Predicates
import Tct.Method.Uncurry
import Tct.Method.DP.UsableRules
import Tct.Method.DP.DependencyPairs
import Tct.Method.DP.PathAnalysis
import qualified Tct.Method.Weightgap as Weightgap
import Tct.Method.DP.DependencyGraph hiding (strict, weak)
import Tct.Method.InnermostRuleRemoval
import Qlogic.NatSat (Size (..))
import qualified Tct.Processor as P
import qualified Tct.Processor.Standard as S
import Tct.Processor (solveBy)
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
                   <|> NaturalMI.matrixProcessor
                   <|> ArcticMI.arcticProcessor
                   <|> Weightgap.weightgapProcessor
                   <|> Compose.composeProcessor
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


-- * defaultMatrix

data DefaultMatrix = DefaultMatrix { kind :: NaturalMI.NaturalMIKind
                                   , dim  :: Int
                                   , degree :: Int
                                   , bits :: Int
                                   , cbits :: Int
                                   , on :: Weightgap.WgOn
                                   , useUsableArgs :: Bool }

instance P.IsDefaultOption DefaultMatrix where 
    defaultOptions = DefaultMatrix { kind = NaturalMI.Automaton
                                   , dim    = error "dimension must be specified"
                                   , degree = error "degree must be specified"
                                   , bits   = 2
                                   , cbits  = 3
                                   , useUsableArgs = True
                                   , on            = Weightgap.WgOnAny }

matrix :: DefaultMatrix -> P.InstanceOf (S.StdProcessor NaturalMI.NaturalMI)
matrix m = S.StdProcessor NaturalMI.NaturalMI `S.withArgs` ((kind m) :+: (Just $ nat $ degree m) :+: (nat $ dim m) :+: (Nat $ bits m) :+: Nothing :+: (Just $ Nat $ cbits m) :+: (useUsableArgs m))


arctic :: DefaultMatrix -> P.InstanceOf (S.StdProcessor ArcticMI.ArcticMI)
arctic m = S.StdProcessor ArcticMI.ArcticMI `S.withArgs` ((nat $ dim m) :+: (Nat $ ArcSat.intbound $ ArcSat.Bits $ bits m) :+: Nothing :+: (Just $ Nat $ cbits m) :+: (useUsableArgs m))


weightgap :: DefaultMatrix -> TheTransformer Weightgap.WeightGap
weightgap m = Weightgap.WeightGap `calledWith` (on m :+: (kind m) :+: (Just $ nat $ degree m) :+: (nat $ dim m) :+: (Nat $ bits m) :+: Nothing :+: (Just $ Nat $ cbits m) :+: (useUsableArgs m))
