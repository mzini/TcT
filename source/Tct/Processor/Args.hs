{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeFamilies #-}
module Tct.Processor.Args 
where

import qualified Tct.Processor as P
import Tct.Processor.Parse
import Text.Parsec.Prim
import Text.Parsec.Combinator
import Text.Parsec.Char
import qualified Data.Map as Map
import Data.Typeable (cast, Typeable)
import Control.Monad (liftM)
import Tct.Main.Debug

data Arg k = Arg { argName         :: String
                 , argDescription  :: String
                 , argDefault      :: A (Arg k)
                 , isOptional      :: Bool}
             deriving Typeable 

arg :: Arg a
arg = Arg { argName         = "unknown"
          , argDescription  = ""
          , argDefault      = error "no default argument given"
          , isOptional      = False}

opt :: Arg a
opt = arg { isOptional = True}

data SomeA = forall a. (Show a, Typeable a) => SomeA a deriving (Typeable)
instance Show SomeA where
    show (SomeA a) = "SomeA " ++ show a

class (Typeable (A a), Show (A a)) => Stub a where
    type A a
    syn :: a -> String


optparser a p = case parseName a of 
                  Just n -> [do _ <- string $ ":" ++ n
                                whiteSpace
                                a' <- p
                                return (n, SomeA a')]
                  Nothing -> []

class Stub a => ParsableStub a where
    parseArg :: a -> Map.Map String SomeA -> P.ProcessorParser (A a)
    parseName :: a -> Maybe String
    optionalParsers :: (Typeable (A a), Show (A a)) => a -> [P.ProcessorParser (String, SomeA)]

newtype Nat = Nat Int deriving (Typeable, Show)
instance Stub (Arg Nat) where
    type A (Arg Nat) = Nat
    syn _ = "<nat>"

instance ParsableStub (Arg Nat) where
    parseName = Just . argName
    parseArg a m | isOptional a = case Map.lookup (argName a) m of 
                                    Just (SomeA n) -> case cast n of 
                                                       Just n' -> return (n' :: Nat)
                                                       Nothing -> return $ Nat 33
                                    Nothing -> return $ Nat 99
                                              
                 | otherwise    = Nat `liftM` natural
    optionalParsers a = optparser a (Nat `liftM` natural)

data a :+: b = a :+: b deriving (Typeable, Show)

instance (Stub a, Stub b) => Stub (a :+: b) where
    type A (a :+: b) = A a :+: A b
    syn (sa :+: sb) = syn sa ++ " " ++ syn sb

instance (ParsableStub a, ParsableStub b) => ParsableStub (a :+: b) where
    parseName = const Nothing
    parseArg (sa :+: sb) opts = do a <- parseArg sa opts
                                   whiteSpace
                                   b <- parseArg sb opts
                                   return (a :+: b)
    optionalParsers (sa :+: sb) = optionalParsers sa ++ optionalParsers sb


parseArguments :: ParsableStub a => a -> P.ProcessorParser (A a)
parseArguments a = do optargs <- Map.fromList `liftM` many (choice $ optparser)
                      parseArg a (unsafeDebugMsg optargs)
    where optparser = [ try $ do r <- p
                                 whiteSpace
                                 return r 
                        | p <- optionalParsers a]
--    parseLst (sa :+: _) = parseLst sa
    -- parseLst a = do _ <- string $ ":" ++ argName a
    --                 whiteSpace
    --                 a' <- parseArg a
    --                 return [SomeA a']
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


-- data a :|: b = a :|: b

-- instance (Stub a, Stub b) => Stub (a :|: b) where
--     type A (a :|: b) = A a :+: A b
--     syn (sa :|: sb) = syn sa ++ " " ++ syn sb -- TODO



-- instance (ParsableStub a, ParsableStub b) => ParsableStub (a :|: b) where
--     parseArg (sa :|: sb) = do a <- parseArg sa
--                               whiteSpace
--                               b <- parseArg sb 
--                               return (a :+: b)
--     parseLst (sa :|: sb) = do es <- many (try (parseLst sa) <|> parseLst sb)
--                               return $ concat es






