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
import Tct.Processor.Args

import Termlib.Problem (Problem)

import Tct.Processor.Parse

data TheProcessor a = TheProcessor { processor     :: a
                                   , processorArgs :: A.A (Arguments a)
                                   }

class (A.Stub (Arguments a)) => Processor a where
    type Arguments a
    type ProofOf a 
    name      :: a -> String
    description :: a -> [String]
    solve     :: TheProcessor a -> Problem -> P.SolverM (ProofOf a)
    arguments :: a -> (Arguments a)

data StdProc a = StdProc a deriving Show

instance Processor a => P.Processor (StdProc a) where
    type P.ProofOf (StdProc a) = ProofOf a
    data P.InstanceOf (StdProc a) = TP (TheProcessor a)
    name (StdProc a) = name a
    description (StdProc a) = description a
    synopsis (StdProc a) = name a ++ " " ++ A.syn (arguments a) 
    solve (TP theproc) prob = solve theproc prob
    fromInstance (TP theproc) = StdProc $ processor theproc
    parseProcessor_ (StdProc a) = do _ <- string (name a)
                                     whiteSpace
                                     args <- A.parseArg (arguments a)
                                     return $ TP $ TheProcessor { processor = a
                                                                , processorArgs = args}

data Foo = Foo

instance Processor Foo where
    type Arguments Foo = (Arg A.Nat) :+: (Arg A.Nat)
    type ProofOf Foo = String :+: (A.Nat :+: A.Nat)
    name Foo = "wdp"
    solve proc _ = return $ "foo" :+: processorArgs proc
    arguments Foo = arg { argName = "slisize"
                        , argDescription = "descr1"}
                    :+: 
                    arg { argName = "arg2"
                        , argDescription = "descr1"
                        }
