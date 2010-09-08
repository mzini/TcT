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
import qualified Tct.Processor.Args as A
import Tct.Processor.Args hiding (name, description, synopsis)
import Data.Typeable 
import Termlib.Problem (Problem)

import Tct.Processor.Parse

data TheProcessor a = TheProcessor { processor     :: a
                                   , processorArgs :: Domains (ArgumentsOf a) }

class StdProcessor a where
    type ArgumentsOf a
    type ProofOf a
    name         :: a -> String
    instanceName :: TheProcessor a -> String
    description  :: a -> [String]
    arguments    :: a -> (ArgumentsOf a)
    solve        :: TheProcessor a -> Problem -> P.SolverM (ProofOf a)


data Processor a = Processor a deriving (Typeable, Show)

instance (StdProcessor a, Arguments (ArgumentsOf a)) => P.Processor (Processor a) where
    type P.ProofOf (Processor a)    = ProofOf a
    data P.InstanceOf (Processor a) = TP (TheProcessor a)
    name (Processor a)            = name a
    instanceName (TP theproc)     = instanceName theproc
    description (Processor a)     = description a
    argDescriptions (Processor a) = [ (adName d, descr d) | d <- descriptions $ arguments a, adIsOptional d]
        where descr d = adDescr d ++ argDescrOnDefault mshow d
                  where mshow Nothing    = "" 
                        mshow (Just def) = "The default is set to '" ++ show def ++ "'."
    solve (TP theproc) prob       = solve theproc prob
--    fromInstance (TP theproc) = Processor $ processor theproc

instance (StdProcessor a, ParsableArguments (ArgumentsOf a)) => P.ParsableProcessor (Processor a) where
    synopsis (Processor a) = name a ++ " " ++ A.synopsis (arguments a) 
    parseProcessor_ (Processor a) = do _ <- string (name a)
                                       whiteSpace
                                       args <- parseArguments (arguments a)
                                       return $ TP $ TheProcessor { processor = a
                                                                  , processorArgs = args}

calledWith :: StdProcessor a => a -> Domains (ArgumentsOf a) -> P.InstanceOf (Processor a)
p `calledWith` a = TP $ TheProcessor { processor = p
                                     , processorArgs = a }



-- tstdata

-- data Foo = Foo


-- instance Answerable (String :+: (Nat :+: Nat)) where
--     answer _ = NoAnswer

-- instance PrettyPrintable (String :+: (Nat :+: Nat)) where
--     pprint n = text $ show n

-- instance ComplexityProof (String :+: (Nat :+: Nat))

-- instance StdProcessor Foo where
--     type ArgumentsOf Foo = (Arg Nat) :+: (Arg Nat)
--     type ProofOf Foo = String :+: (Nat :+: Nat)
--     name Foo = "wdp"
--     description Foo = ["leaf processor"]
--     solve proc _ = return $ "foo" :+: processorArgs proc
--     arguments Foo = opt { A.name = "slisize"
--                         , A.description = ["descr1"]
--                         , A.defaultValue     = Nat 42}
--                     :+: 
--                     arg { A.name = "arg2"
--                         , A.description = ["descr2"]
--                         }


-- processorFoo :: Processor Foo
-- processorFoo = Processor Foo


-- data Bar p = Bar

-- data BarProof a = BarProof Nat (P.ProofOf a)
-- instance P.Processor a => StdProcessor (Bar a) where
--     type ArgumentsOf (Bar a) = (Arg (Processor a)) :+: (Arg Nat)
--     type ProofOf (Bar a) = BarProof a
--     name Bar = "bar"
--     description Bar = ["i am bar"]
--     solve proc prob = do r <- P.solve proc' prob
--                          return $ BarProof n r
--         where proc' :+: n = processorArgs proc
--     arguments Bar = arg { A.name = "subproc"
--                         , A.description = ["some subprocessor"] }
--                     :+: 
--                     opt { A.name = "natural"
--                         , A.description = ["somenaturalnumber"]
--                         , A.defaultValue = Nat 47}


-- instance Answerable (P.ProofOf a) => Answerable (BarProof a) where
--     answer (BarProof _ a) = answer a

-- instance PrettyPrintable (P.ProofOf a) => PrettyPrintable (BarProof a) where
--     pprint (BarProof n p) = (text $ show n) $$ pprint p

-- instance (PrettyPrintable (P.ProofOf a), Answerable (P.ProofOf a)) => ComplexityProof (BarProof a)


-- bar :: P.Processor p => P.InstanceOf p -> Nat -> P.InstanceOf (Processor (Bar p))
-- bar p n = Bar `calledWith` (p :+: n)


-- processorBar :: Processor (Bar P.AnyProcessor)
-- processorBar  = Processor Bar
