{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeFamilies #-}
module Tct.Processor.StdProcessor where

import qualified Tct.Strategy.Default as P
import Tct.Processor.Args
import Tct.Strategy.Parse
import Text.ParserCombinators.Parsec
import Termlib.Problem (Problem)


data TheProcessor a = TheProcessor { processor     :: a
                                   , processorArgs :: Arguments a
                                   }

class (ParsableArgument (Arguments a)) => StdProcessor a where
    type Arguments a
    type Proof a 
    name      :: a -> String
    solve     :: TheProcessor a -> Problem -> P.SolverM (Proof a)
    arguments :: a -> StubOf (Arguments a)

data StdProc a = StdProc a
instance StdProcessor a => P.Processor (StdProc a) where
    type P.Proof (StdProc a) = Proof a
    data P.Instance (StdProc a) = TP (TheProcessor a)
    name (StdProc a) = name a
    solve (TP theproc) prob = solve theproc prob
    parseProcessor (StdProc a) = do _ <- string (name a)
                                    whiteSpace
                                    args <- parseArg (arguments a)
                                    return $ TP $ TheProcessor { processor = a
                                                               , processorArgs = args}


arg :: Arg a
arg = Arg { argname = "unknown"
          , description = ""
          , defaultValue = error "no default value given"}


data Foo = Foo

instance StdProcessor Foo where
    type Arguments Foo = Nat :+: Optional Nat
    type Proof Foo = String :+: (Nat :+: Optional Nat)
    name Foo = "wdp"
    solve proc _ = return $ "foo" :+: processorArgs proc
    arguments Foo = arg { argname = "slisize"
                        , description = "descr1"}
                    :+: 
                    arg { argname = "arg2"
                        , description = "descr1"
                        , defaultValue = Nat 3
                        }
