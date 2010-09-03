{-# LANGUAGE UndecidableInstances #-}
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
    -- ( processor
    -- , processorArgs
    -- , TheProcessor
    -- , Processor (..))
where

import Text.ParserCombinators.Parsec

import qualified Tct.Processor as P
import Tct.Proof -- TODO
import Termlib.Utils (PrettyPrintable(..)) -- TODO
import Tct.Certificate -- TODO
import System.IO.Unsafe (unsafePerformIO) -- TODO
import Text.PrettyPrint.HughesPJ
import qualified Tct.Processor.Args as A
import Tct.Processor.Args

import Termlib.Problem (Problem)

import Tct.Processor.Parse

data TheProcessor a = TheProcessor { processor     :: a
                                   , processorArgs :: A.A (Arguments a)
                                   }

class Processor a where
    type Arguments a
    type ProofOf a 
    name      :: a -> String
    description :: a -> [String]
    solve     :: TheProcessor a -> Problem -> P.SolverM (ProofOf a)
    arguments :: a -> (Arguments a)

data StdProc a = StdProc a deriving Show

instance (Processor a, Stub (Arguments a)) => P.Processor (StdProc a) where
    type P.ProofOf (StdProc a) = ProofOf a
    data P.InstanceOf (StdProc a) = TP (TheProcessor a)
    name (StdProc a) = name a
    description (StdProc a) = description a
    solve (TP theproc) prob = solve theproc prob
    fromInstance (TP theproc) = StdProc $ processor theproc

instance (Processor a, ParsableStub (Arguments a)) => P.ParsableProcessor (StdProc a) where
    synopsis (StdProc a) = name a ++ " " ++ A.syn (arguments a) 
    parseProcessor_ (StdProc a) = do _ <- string (name a)
                                     whiteSpace
                                     args <- A.parseArg (arguments a)
                                     return $ TP $ TheProcessor { processor = a
                                                                , processorArgs = args}


data P a = P a 
instance P.Processor a => Stub (Arg (P a)) where
    type A (Arg (P a)) = P.InstanceOf a
    syn _ = "<processor>"

instance ParsableStub (Arg (P P.AnyProcessor)) where
    parseArg _ = P.parseAnyProcessor

data Foo = Foo


instance Answerable (String :+: (Nat :+: Nat)) where
    answer _ = FailAnswer

instance PrettyPrintable (String :+: (Nat :+: Nat)) where
    pprint _ = text "string :+: nat :+: nat"

instance ComplexityProof (String :+: (Nat :+: Nat))

instance Processor Foo where
    type Arguments Foo = (Arg Nat) :+: (Arg Nat)
    type ProofOf Foo = String :+: (Nat :+: Nat)
    name Foo = "wdp"
    description Foo = ["leaf processor"]
    solve proc _ = return $ "foo" :+: processorArgs proc
    arguments Foo = arg { argName = "slisize"
                        , argDescription = "descr1"}
                    :+: 
                    arg { argName = "arg2"
                        , argDescription = "descr1"
                        }

data Bar p = Bar

instance P.Processor a => Processor (Bar a) where
    type Arguments (Bar a) = (Arg (P a)) :+: (Arg Nat)
    type ProofOf (Bar a) = P.ProofOf a
    name Bar = "bar"
    description Bar = ["i am bar"]
    solve proc prob = P.solve proc' prob
        where proc' :+: _ = processorArgs proc
    arguments Bar = arg { argName = "subproc"
                        , argDescription = "some subprocessor" }
                    :+: 
                    arg { argName = "a natural"
                        , argDescription = "somenaturalnumber"}


someBar :: StdProc (Bar P.AnyProcessor)
someBar  = StdProc Bar


pp :: P.AnyProcessor
pp = P.anyOf [ P.some (StdProc Foo)
             , P.some someBar]
