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

module Tct.Strategy.Arg 
    (Arg (..)
    , mkParseSomeProcessor)
where

import Data.Typeable
import Control.Monad (liftM)
import Text.ParserCombinators.Parsec hiding (parse)

import Tct.Strategy (StrategyParser, parseSomeProcessor, Strategy)
import Tct.Strategy.Parse 
import qualified Tct.Strategy as S
import Tct.Strategy.Flag (Flags, parseFlags)
import Tct.Processor.SomeProcessor (SomeProcessor(..))
import Tct.Processor (Processor)

class (Typeable a) => Arg a where
    parseArg   :: StrategyParser a
    synopsis   :: a -> String

newtype Natural = N Int deriving Typeable

instance Arg Natural where
    parseArg = (N . read) `liftM` many1 digit
    synopsis _ = "<nat>"

instance Arg () where
    parseArg = return ()
    synopsis () = ""

instance (Arg a, Arg b) => Arg (a,b) where 
    parseArg = do a <- parseArg
                  _ <- many1 (oneOf " \t")
                  b <- parseArg
                  return (a,b)
    synopsis (_ :: (a,b)) = synopsis (undefined :: a) ++ " " ++ synopsis (undefined :: b)                  

instance (Arg a) => Arg [a] where
    parseArg = many1 $ do a <- parseArg
                          try whiteSpace
                          return a
    synopsis (_ :: [a]) = synopsis (undefined :: a) ++ "^*"

instance Arg SomeProcessor where
    parseArg = parseSomeProcessor
    synopsis _ = "<processor>"

mkParseSomeProcessor :: (Strategy strat, Processor proc, Arg a) => 
                        strat -> ((Flags, a) -> proc) -> StrategyParser SomeProcessor
mkParseSomeProcessor strat mkProc = do _ <- try $ string $ S.strategyName strat
                                       try whiteSpace
                                       parsedFlags <- parseFlags $ S.flags strat
                                       args <- parseArg
                                       return $ SomeProcessor $ mkProc (parsedFlags,args)

