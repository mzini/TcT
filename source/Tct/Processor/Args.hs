{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeFamilies #-}
module Tct.Processor.Args 
where

import Tct.Processor
import Tct.Processor.Parse
import Text.ParserCombinators.Parsec hiding (parse)
import Control.Monad (liftM)


data Arg k = Arg { argName         :: String
                 , argDescription  :: String
                 , argDefaultValue :: k}

arg :: Arg a
arg = Arg { argName         = "unknown"
          , argDescription  = ""
          , argDefaultValue = error "no default value given"}

class ParsableArgument a where 
    type StubOf a
    syn :: (StubOf a) -> String
    parseArg :: StubOf a -> ProcessorParser a

instance Processor p => ParsableArgument (InstanceOf p) where
    type StubOf (InstanceOf p) = p
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
    syn _ = "[" ++ syn (undefined :: StubOf a) ++ "]"
    parseArg a = try (Specified `liftM` pa) <|> (return $ Default $ argDefaultValue a)
        where pa = do _ <- char ':' 
                      _ <- string (argName a)
                      whiteSpace
                      parseArg (undefined :: a)

data a :+: b = a :+: b

instance (ParsableArgument a, ParsableArgument b) => ParsableArgument (a :+: b) where
    type StubOf (a :+: b) = StubOf a :+: StubOf b
    syn ((sa :: StubOf a) :+: sb) = syn sa ++ " " ++ syn sb
    parseArg (sa :+: sb) = do a <- parseArg sa
                              whiteSpace
                              b <- parseArg sb 
                              return (a :+: b)

