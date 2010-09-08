{-# LANGUAGE ScopedTypeVariables #-}
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

module Tct.Processor.Args.Instances where

import Data.Typeable
import Control.Monad (liftM)
import Text.Parsec.Prim (many, try, (<|>))
import Tct.Processor.Parse
import Tct.Processor.Args
import qualified Tct.Processor as P
import Tct.Processor.Standard

newtype Nat = Nat Int deriving (Typeable, Show)

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

instance (Typeable (P.InstanceOf a), P.Processor a, Show (P.InstanceOf a)) => Argument (Processor a) where
    type Domain (Processor a) = P.InstanceOf a
    domainName _ = "<processor>"

instance ParsableArgument (Processor P.AnyProcessor) where
    parseArg Phantom = P.parseAnyProcessor

instance Argument a => Argument [a] where 
    type Domain [a] = [Domain a]
    domainName Phantom =  "<" ++ domainName (Phantom :: Phantom a) ++ " list" ++ ">" 

instance ParsableArgument a => ParsableArgument [a] where
    parseArg Phantom = many p 
        where p :: P.ProcessorParser (Domain a)
              p = do r <- parseArg (Phantom :: Phantom a)
                     try whiteSpace <|> return ()
                     return r

