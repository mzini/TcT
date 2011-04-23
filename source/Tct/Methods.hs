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
    (  -- *  Parsable Processors
     failProcessor
    , bestProcessor
    , boundsProcessor
    , composeProcessor
    , epostarProcessor
    , fastestProcessor
    , iteProcessor
    , irrProcessor
    , lmpoProcessor
    , matrixProcessor
    , arcticProcessor
    , popstarProcessor
    , sequentiallyProcessor
    , successProcessor
    , timeoutProcessor
    , predicateProcessors
    , uncurryProcessor
    , wdgProcessor
    , (<|>)
    -- * Processors
    , arctic
    , best
    , bounds
    , composeDynamic
    , composeStatic
    , epostar
    , empty
    , fail
    , fastest
    , ite
    , irr
    , matrix
    , popstar
    , sequentially
    , success
    , timeout
    , uncurry
    , wdg
    , CustomProcessor
    , CPConfig(..)
    , custom
    , customProcessor

    -- * Predicates
    , isDuplicating
    , isConstructor
    , isCollapsing
    , isLeftLinear
    , isRightLinear
    , isWellFormed

    -- * Processor Combinators and Utilities
    , withArgs
    , upto
    , solveBy
    , orFaster
    , orBetter
    , before

    -- ** Argument Types
    , Arg (..)
    , Unit
    , (:+:)(..)
    , EnumArg
    , Proc
    , Approximation(..)
    , natural
    , bool
    , some
    , processor
    , optional
    , arg
    , opt
    , unit

    -- ** Argument Construction
    , NaturalMIKind (..)
    , Size (..)
    , nat
    , Nat (..)
    , Enrichment (..)
    , InitialAutomaton (..)

    -- ** The Default Processor Used by TCT
    , builtInProcessors
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
import Tct.Method.Wdg
import Tct.Method.InnermostRuleRemoval
import Qlogic.NatSat (Size (..))
import qualified Tct.Processor as P
import Tct.Processor (solveBy)
import qualified Tct.Processor.Standard as S
import Tct.Processor.Standard (withArgs)
import Tct.Processor.Args
import Tct.Processor.Args.Instances

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
                   <|> wdgProcessor
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


