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

{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeFamilies #-}

module Tct.Processor.Standard 
    ( processor
    , processorArgs
    , TheProcessor
    , Processor (..))
where

import Text.ParserCombinators.Parsec

import qualified Tct.Processor as P
import qualified Tct.Processor.Args as A

import Termlib.Problem (Problem)

import Tct.Processor.Parse

data TheProcessor a = TheProcessor { processor     :: a
                                   , processorArgs :: Arguments a
                                   }

class (A.ParsableArgument (Arguments a)) => Processor a where
    type Arguments a
    type Proof a 
    name      :: a -> String
    description :: a -> [String]
    solve     :: TheProcessor a -> Problem -> P.SolverM (Proof a)
    arguments :: a -> A.StubOf (Arguments a)

data StdProc a = StdProc a deriving Show

instance Processor a => P.Processor (StdProc a) where
    type P.Proof (StdProc a) = Proof a
    data P.Instance (StdProc a) = TP (TheProcessor a)
    name (StdProc a) = name a
    solve (TP theproc) prob = solve theproc prob
    parseProcessor (StdProc a) = do _ <- string (name a)
                                    whiteSpace
                                    args <- A.parseArg (arguments a)
                                    return $ TP $ TheProcessor { processor = a
                                                               , processorArgs = args}

-- data Foo = Foo

-- instance StdProcessor Foo where
--     type Arguments Foo = Nat :+: Optional Nat
--     type Proof Foo = String :+: (Nat :+: Optional Nat)
--     name Foo = "wdp"
--     solve proc _ = return $ "foo" :+: processorArgs proc
--     arguments Foo = arg { argname = "slisize"
--                         , description = "descr1"}
--                     :+: 
--                     arg { argname = "arg2"
--                         , description = "descr1"
--                         , defaultValue = Nat 3
--                         }
