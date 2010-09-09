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
newtype Nat = Nat Int deriving (Typeable)


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
instance (Typeable (P.InstanceOf a), P.Processor a, Show (P.InstanceOf a)) => Argument (Processor a) where
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

instance (Typeable a, Show a, Enum a, Bounded a) => Argument (EnumOf a) where
    type Domain (EnumOf a) = a
    domainName Phantom = br $ concat $ intersperse "|" [ show e | e <- [(minBound :: a) .. maxBound] ]
        where br s = "[" ++ s ++ "]"

instance (Typeable a, Show a, Enum a, Bounded a) => ParsableArgument (EnumOf a) where
    parseArg Phantom = choice [ try $ pa (show e) e | e <- [(minBound :: a) .. maxBound] ]
        where pa n e = do _ <- string n
                          return e


