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
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE UndecidableInstances #-}

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
import Data.Typeable 
import Termlib.Problem (Problem)

import Tct.Processor.Parse

data TheProcessor a = TheProcessor { processor     :: a
                                   , processorArgs :: A.A (Arguments a)
                                   }


-- type family Fn a b 

-- type instance Fn () b = b
-- type instance Fn (a :+: b) r = a -> (Fn b r)



class StdProcessor a where
    type Arguments a
    type ProofOf a 
    name      :: a -> String
    description :: a -> [String]
    solve     :: TheProcessor a -> Problem -> P.SolverM (ProofOf a)
--    s :: a -> Problem -> Fn (Arguments a) (P.SolverM (ProofOf a))
    arguments :: a -> (Arguments a)

data Processor a = Processor a deriving (Typeable, Show)

instance (StdProcessor a, Stub (Arguments a)) => P.Processor (Processor a) where
    type P.ProofOf (Processor a) = ProofOf a
    data P.InstanceOf (Processor a) = TP (TheProcessor a)
    name (Processor a) = name a
    description (Processor a) = description a
    solve (TP theproc) prob = solve theproc prob
    fromInstance (TP theproc) = Processor $ processor theproc

instance (StdProcessor a, ParsableStub (Arguments a)) => P.ParsableProcessor (Processor a) where
    synopsis (Processor a) = name a ++ " " ++ A.syn (arguments a) 
    parseProcessor_ (Processor a) = do _ <- string (name a)
                                       whiteSpace
                                       args <- parseArguments (arguments a)
                                       return $ TP $ TheProcessor { processor = a
                                                                  , processorArgs = args}


instance (Typeable (P.InstanceOf a), P.Processor a, Show (P.InstanceOf a)) => Stub (Arg (Processor a)) where
    type A (Arg (Processor a)) = P.InstanceOf a
    syn _ = "<processor>"

instance ParsableStub (Arg (Processor P.AnyProcessor)) where
    parseName = Just . argName
    parseArg _ _ = P.parseAnyProcessor
    optionalParsers a = optparser a P.parseAnyProcessor
data Foo = Foo


instance Answerable (String :+: (Nat :+: Nat)) where
    answer _ = FailAnswer

instance PrettyPrintable (String :+: (Nat :+: Nat)) where
    pprint n = text $ show n

instance ComplexityProof (String :+: (Nat :+: Nat))

instance StdProcessor Foo where
    type Arguments Foo = (Arg Nat) :+: (Arg Nat)
    type ProofOf Foo = String :+: (Nat :+: Nat)
    name Foo = "wdp"
    description Foo = ["leaf processor"]
    solve proc _ = return $ "foo" :+: processorArgs proc
    arguments Foo = opt { argName = "slisize"
                        , argDescription = "descr1"
                        , argDefault     = Nat 42}
                    :+: 
                    arg { argName = "arg2"
                        , argDescription = "descr1"
                        }


processorFoo :: Processor Foo
processorFoo = Processor Foo


data Bar p = Bar

data BarProof a = BarProof Nat (P.ProofOf a)
instance P.Processor a => StdProcessor (Bar a) where
    type Arguments (Bar a) = (Arg (Processor a)) :+: (Arg Nat)
    type ProofOf (Bar a) = BarProof a
    name Bar = "bar"
    description Bar = ["i am bar"]
    solve proc prob = do r <- P.solve proc' prob
                         return $ BarProof n r
        where proc' :+: n = processorArgs proc
    arguments Bar = arg { argName = "subproc"
                        , argDescription = "some subprocessor" }
                    :+: 
                    opt { argName = "natural"
                        , argDescription = "somenaturalnumber"
                        , argDefault = Nat 47}


instance Answerable (P.ProofOf a) => Answerable (BarProof a) where
    answer (BarProof _ a) = answer a

instance PrettyPrintable (P.ProofOf a) => PrettyPrintable (BarProof a) where
    pprint (BarProof n p) = (text $ show n) $$ pprint p

instance (PrettyPrintable (P.ProofOf a), Answerable (P.ProofOf a)) => ComplexityProof (BarProof a)



calledWith :: StdProcessor a => a -> A (Arguments a) -> P.InstanceOf (Processor a)
p `calledWith` a = TP $ TheProcessor { processor = p
                                     , processorArgs = a }


-- class F a b | a -> b where
--     call :: a -> b

-- instance F (p, (a :+: b)) r => F (p, a) (b -> r) where
--     call (p,a) = undefined -- \ b -> call (p,(a :+: b))

bar :: P.Processor p => P.InstanceOf p -> Nat -> P.InstanceOf (Processor (Bar p))
bar p n = Bar `calledWith` (p :+: n)


processorBar :: Processor (Bar P.AnyProcessor)
processorBar  = Processor Bar

-- proc :: (StdProcessor a, ParsableStub (Arguments a), ComplexityProof (ProofOf a)) => a -> P.SomeProcessor
-- proc = P.some . Processor

pp :: P.AnyProcessor
pp = P.anyOf [ P.some processorFoo
             , P.some processorBar]
