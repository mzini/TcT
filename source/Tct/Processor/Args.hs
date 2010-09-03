{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeFamilies #-}
module Tct.Processor.Args 
where

import qualified Tct.Processor as P
import Tct.Processor.Parse
-- import Control.Monad (liftM)


data Arg k = Arg { argName         :: String
                 , argDescription  :: String}

arg :: Arg a
arg = Arg { argName         = "unknown"
          , argDescription  = ""}

class Stub a where
    type A a
    syn :: a -> String

class Stub a => ParsableStub a where
    parseArg :: a -> P.ProcessorParser (A a)

newtype Nat = Nat Int
instance Stub (Arg Nat) where
    type A (Arg Nat) = Nat
    syn _ = "<nat>"
instance ParsableStub (Arg Nat) where
    parseArg _ = do n <- natural
                    return $ Nat n

-- instance Stub (Arg Bool) where
--     type A (Arg Bool) = Bool
--     syn _ = "<nat>"
--     parseArg _ = do n <- try (string "On") <|> string "Off"
--                     return $ if n == "On" then True else False
                               

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

instance (ParsableStub a, ParsableStub b) => ParsableStub (a :+: b) where
    parseArg (sa :+: sb) = do a <- parseArg sa
                              whiteSpace
                              b <- parseArg sb 
                              return (a :+: b)

