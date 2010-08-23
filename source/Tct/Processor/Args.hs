{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeFamilies #-}
module Tct.Processor.Args where

import Tct.Strategy.Default
import Tct.Strategy.Parse
import Text.ParserCombinators.Parsec hiding (parse)
import Control.Monad (liftM)


data Arg k = Arg { argname      :: String
                 , description  :: String
                 , defaultValue :: k
                 }

type family StubOf a


class ParsableArgument a where 
    syn :: a -> String
    parseArg :: StubOf a -> ProcessorParser a


type instance StubOf (Instance p) = p
instance Processor p => ParsableArgument (Instance p) where
    syn _ = "<processor>"
    parseArg p = parseProcessor p

newtype Nat = Nat Int

type instance StubOf Nat = Arg Nat

instance ParsableArgument Nat where
    syn _ = "<nat>"
    parseArg _ = do n <- natural
                    return $ Nat n
                               

data Optional a = Specified a 
                | Default a

type instance StubOf (Optional a) = Arg a

instance ParsableArgument a => ParsableArgument (Optional a) where
    syn _ = "[" ++ (undefined :: a) ++ "]"
    parseArg a = try (Specified `liftM` pa) <|> (return $ Default $ defaultValue a)
        where pa = do _ <- char ':' 
                      _ <- string (argname a)
                      whiteSpace
                      parseArg (undefined :: a)

data a :+: b = a :+: b

type instance StubOf (a :+: b) = StubOf a :+: StubOf b

instance (ParsableArgument a, ParsableArgument b) => ParsableArgument (a :+: b) where
    syn (sa :+: sb) = syn sa ++ " " ++ syn sb
    parseArg (sa :+: sb) = do a <- parseArg sa
                              whiteSpace
                              b <- parseArg sb 
                              return (a :+: b)

