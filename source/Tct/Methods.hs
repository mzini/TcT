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
    , predicateProcessors
    , uncurryProcessor
    , wdgProcessor
    , customProcessor
    , (<|>)
    -- * Processors
    , arctic
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
    , uncurry
    , wdg
    , Approximation(..)
    , CustomProcessor(..)
    -- * Predicates
    , isDuplicating
    , isConstructor
    , isCollapsing
    , isLeftLinear
    , isRightLinear
    , isWellFormed

    -- * Processor Combinators and Utilities
    , call
    , upto

    -- ** Argument Types
    , Arg
    , Unit
    , (:+:)(..)
    , EnumArg
    , NaturalArg
    , BoolArg
    , ProcessorArg
    , natural
    , bool
    , processor
    , optional
    , unit

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
import Prelude hiding (fail, uncurry)

import Tct.Method.Combinator
import Tct.Method.PopStar
import Tct.Method.EpoStar
import Tct.Method.Combine
import Tct.Method.Bounds
import Tct.Method.Matrix.ArcticMI
import Tct.Method.Matrix.NaturalMI
import Tct.Method.Custom
import Tct.Method.Predicates
import Tct.Method.Uncurry
import Tct.Method.Wdg
import Qlogic.NatSat (Size (..))
import qualified Tct.Processor as P
import qualified Tct.Processor.Standard as S
import Tct.Proof
import Tct.Processor.Args
import Tct.Processor.Args.Instances

import Tct.Processor.Timeout
import Tct.Processor (none, (<|>), AnyProcessor)

defaultProcessor :: AnyProcessor
defaultProcessor = timeoutProcessor
                   <|> failProcessor 
                   <|> successProcessor
                   <|> iteProcessor
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
                   <|> combineProcessor
                   <|> foldr (<|>) none predicateProcessors

-- combinators

call :: (P.ComplexityProcessor p) => P.InstanceOf p -> P.InstanceOf P.SomeProcessor
call = P.someInstance

upto :: (Enum n, Ord n, ComplexityProof (P.ProofOf p), P.Processor p) =>
        (n -> P.InstanceOf p) -> (Bool :+: n :+: n) -> P.InstanceOf (S.Processor (OneOf p))
upto prc (fast :+: l :+: u) | l > u     = fastest []
                            | fast      = fastest subs
                            | otherwise = sequentially subs
    where subs = [ prc i | i <- [l..u] ]
