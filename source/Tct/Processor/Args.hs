{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeFamilies #-}
module Tct.Processor.Args 
where

import Tct.Processor.Standard
import Tct.Strategy.Parse
import Text.ParserCombinators.Parsec hiding (parse)
import Control.Monad (liftM)


data Arg k = Arg { argname      :: String
                 , description  :: String
                 , defaultValue :: k
                 }

arg :: Arg a
arg = Arg { argname = "unknown"
          , description = ""
          , defaultValue = error "no default value given"}

class ParsableArgument a where 
    type StubOf a
    syn :: a -> String
    parseArg :: StubOf a -> ProcessorParser a

instance Processor p => ParsableArgument (Instance p) where
    type StubOf (Instance p) = p
    syn _ = "<processor>"
    parseArg p = parseProcessor p


newtype Nat = Nat Int

instance ParsableArgument Nat where
    type StubOf Nat = Arg Nat
    syn _ = "<nat>"
    parseArg _ = do n <- natural
                    return $ Nat n
                               

data Optional a = Specified a 
                | Default a

instance ParsableArgument a => ParsableArgument (Optional a) where
    type StubOf (Optional a) = Arg a
    syn _ = "[" ++ (undefined :: a) ++ "]"
    parseArg a = try (Specified `liftM` pa) <|> (return $ Default $ defaultValue a)
        where pa = do _ <- char ':' 
                      _ <- string (argname a)
                      whiteSpace
                      parseArg (undefined :: a)

data a :+: b = a :+: b

instance (ParsableArgument a, ParsableArgument b) => ParsableArgument (a :+: b) where
    type StubOf (a :+: b) = StubOf a :+: StubOf b
    syn (sa :+: sb) = syn sa ++ " " ++ syn sb
    parseArg (sa :+: sb) = do a <- parseArg sa
                              whiteSpace
                              b <- parseArg sb 
                              return (a :+: b)

