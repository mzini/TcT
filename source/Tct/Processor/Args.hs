{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeFamilies #-}
module Tct.Processor.Args 
where

import Tct.Processor
import Tct.Processor.Parse
import Tct.Processor.SomeProcessor
import Text.ParserCombinators.Parsec hiding (parse)
import Control.Monad (liftM)


data Arg k = Arg { argName         :: String
                 , argDescription  :: String}

arg :: Arg a
arg = Arg { argName         = "unknown"
          , argDescription  = ""}

-- class ParsableArgument a where 
--     type StubOf a
--     parseArg :: StubOf a -> ProcessorParser a

class Stub a where
    type A a
    syn :: a -> String
    parseArg :: a -> ProcessorParser (A a)

instance Stub SomeProcessor where
    type A SomeProcessor = InstanceOf SomeProcessor
    syn _ = "<processor>"
    parseArg p = parseProcessor p


newtype Nat = Nat Int

instance Stub (Arg Nat) where
    type A (Arg Nat) = Nat
    syn _ = "<nat>"
    parseArg _ = do n <- natural
                    return $ Nat n
                               

-- data Optional stub = Optional { argument :: stub
--                               , defaultValue :: A stub}

-- data OptionalArg a = Specified a 
--                    | Default a

-- instance (Stub a) => Stub (Optional a) where
--     type A (Optional a) = OptionalArg (A a)
--     syn (Optional a _) = "[" ++ syn a ++ "]"
--     parseArg (Optional a def) = try (Specified `liftM` pa) <|> (return $ Default $ def)
--         where pa = do _ <- char ':' 
--                       _ <- string (argName a)
--                       whiteSpace
--                       parseArg a

data a :+: b = a :+: b

instance (Stub a, Stub b) => Stub (a :+: b) where
    type A (a :+: b) = A a :+: A b
    syn (sa :+: sb) = syn sa ++ " " ++ syn sb
    parseArg (sa :+: sb) = do a <- parseArg sa
                              whiteSpace
                              b <- parseArg sb 
                              return (a :+: b)

