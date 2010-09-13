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
    , (<|>)
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
    , custom
    , Custom(..)

    -- * Processor Combinators and Utilities
    , call -- ^ this function translates processor instances to SomeInstances
    , upto -- ^ 'apply processors iteratively

    -- ** Argument Types
    , Arg
    , (:+:)(..)
    , natural
    , bool
    , optional

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
import Prelude hiding (fail)

import Tct.Method.Combinator
import Tct.Method.PopStar
import Tct.Method.EpoStar
import Tct.Method.Combine
import Tct.Method.Bounds
import Tct.Method.Matrix.NaturalMI
import Tct.Method.Macro
import Qlogic.NatSat (Size (..))
import qualified Tct.Processor as P
import qualified Tct.Processor.Standard as S
import Data.Typeable
import Tct.Proof
import Tct.Processor.Args
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

-- combinators

call :: (ComplexityProof (P.ProofOf p), P.Processor p) => P.InstanceOf p -> P.InstanceOf P.SomeProcessor
call = P.someInstance

upto :: (Enum n, Ord n, ComplexityProof (P.ProofOf p), P.Processor p, Show (P.InstanceOf p), Typeable (P.InstanceOf p)) => 
        (n -> P.InstanceOf p) -> (Bool :+: n :+: n) -> P.InstanceOf (S.Processor (OneOf p))
upto proc (fast :+: l :+: u) | l > u     = fastest []
                             | fast      = fastest subs 
                             | otherwise = sequentially subs
    where subs = [ proc i | i <- [l..u] ]


-- argument types

natural :: Arg Nat
natural = arg

bool :: Arg Bool
bool = arg

optional :: Arg t -> String -> Domain t -> Arg t
optional tpe nm def = tpe { name = nm
                          , defaultValue = def
                          , isOptional_ = True}

