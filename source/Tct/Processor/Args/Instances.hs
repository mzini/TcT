{-# LANGUAGE GeneralizedNewtypeDeriving #-}
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

{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Tct.Processor.Args.Instances where

import Data.Typeable
import Control.Monad (liftM)
import Text.Parsec.Combinator (choice)
import Text.Parsec.Char (string)
import Data.List (intersperse)
import Text.Parsec.Prim (many, try, (<|>))
import Tct.Processor.Parse
import Tct.Processor.Args
import qualified Tct.Processor as P
import Tct.Processor.Standard

-- * Primitives
newtype Nat = Nat Int deriving (Typeable, Eq, Ord, Num, Enum)


nat :: Int -> Nat
nat i | i < 0 = error "nat received negative integer"
      | otherwise = Nat i

instance Show Nat where
    show (Nat i) = show i

instance Argument Nat where
    type Domain Nat = Nat
    domainName Phantom = "<nat>"

instance ParsableArgument Nat where
    parseArg Phantom = Nat `liftM` natural

instance Argument Bool where
    type Domain Bool = Bool
    domainName Phantom = "<bool>"

instance ParsableArgument Bool where
    parseArg Phantom = bool


-- * Processors
instance (P.Processor a) => Argument (Processor a) where
    type Domain (Processor a) = P.InstanceOf a
    domainName _ = "<processor>"

instance ParsableArgument (Processor P.AnyProcessor) where
    parseArg Phantom = P.parseAnyProcessor

-- * Compound

instance Argument a => Argument [a] where 
    type Domain [a] = [Domain a]
    domainName Phantom =  "[" ++ domainName (Phantom :: Phantom a) ++ "...]"

instance Argument a => Argument (Maybe a) where 
    type Domain (Maybe a) = Maybe (Domain a)
    domainName Phantom = "[" ++ domainName (Phantom :: Phantom a) ++ "|none]"

instance ParsableArgument a => ParsableArgument (Maybe a) where 
    parseArg Phantom = try (string "none" >> return Nothing)
                       <|> Just `liftM` parseArg (Phantom :: Phantom a)

instance ParsableArgument a => ParsableArgument [a] where
    parseArg Phantom = many p 
        where p :: P.ProcessorParser (Domain a)
              p = do r <- parseArg (Phantom :: Phantom a)
                     try whiteSpace <|> return ()
                     return r

newtype EnumOf a = EnumOf a    

domainNameList :: Show e => [e] -> String
domainNameList l = br $ concat $ intersperse "|" [ show e | e <- l ]
        where br s = "[" ++ s ++ "]"

parseArgAssoc :: [(String,e)] -> P.ProcessorParser e
parseArgAssoc  l = choice [ try $ pa n e | (n,e) <- l]
        where pa n e = do _ <- string n
                          return e

instance (Typeable a, Show a, Enum a, Bounded a) => Argument (EnumOf a) where
    type Domain (EnumOf a) = a
    domainName Phantom = domainNameList [(minBound :: a) .. maxBound]

instance (Typeable a, Show a, Enum a, Bounded a) => ParsableArgument (EnumOf a) where
    parseArg Phantom = parseArgAssoc [(show e, e) | e <- [(minBound :: a) .. maxBound]]

newtype Assoc a = Assoc a

class AssocArg a where 
    assoc :: Phantom a -> [(String, a)]

instance AssocArg a => Argument (Assoc a) where
    type Domain (Assoc a) = a
    domainName _ = domainNameList [ s | (s,_) <- assoc (Phantom :: Phantom a)]

instance AssocArg a => ParsableArgument (Assoc a) where
    parseArg _ = parseArgAssoc $ assoc (Phantom :: Phantom a)

-- type instance CoDomain Nat = Nat

-- class Parsable a where
--     syn   :: a -> String
--     parse :: P.ProcessorParser a

-- instance (ParsableArgument (CoDomain a), Domain (CoDomain a) ~ a) => Parsable a where
--     parse = parseArg (Phantom :: Phantom (CoDomain a))
--     syn   = const $ domainName (Phantom :: Phantom (CoDomain a))

-- foo :: P.ProcessorParser Nat
-- foo = parse 