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

{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

module Tct.Processor.Args where

import qualified Tct.Processor as P
import Tct.Processor.Parse
import Text.Parsec.Prim
import Text.Parsec.Combinator
import Text.Parsec.Char
--import qualified Control.Exception as Ex
import qualified Data.Map as Map
import Data.List (partition, intersperse)
import Data.Typeable (cast, Typeable)
import Control.Monad (liftM)
import Data.Char (toLower)
import Data.Maybe (fromMaybe)
import Text.PrettyPrint.HughesPJ
import qualified Termlib.Utils as U
-- single argument
data Phantom k = Phantom

class Argument a where
    type Domain a
    domainName :: Phantom a -> String
    showArg :: Phantom a -> Domain a -> String

class (Argument a) => ParsableArgument a where
    parseArg :: Phantom a -> P.ProcessorParser (Domain a)
    parseArgInteractive :: Phantom a -> P.AnyProcessor -> IO (Maybe (Domain a))
    parseArgInteractive pa procs = pse `liftM` getLine
      where pse str = 
              case fromString (parseArg pa) procs "argument" str of
                Right a -> Just a
                Left _ -> Nothing
        
data SomeDomainElt = forall a. (Show a, Typeable a) => SomeDomainElt a deriving (Typeable)
instance Show SomeDomainElt where show (SomeDomainElt e) = show e
type ParsedOptionals = Map.Map String SomeDomainElt
type OptionalParser = P.ProcessorParser (String, SomeDomainElt)

class Arguments a where
    type Domains a 

class Arguments a => ParsableArguments a where
    descriptions :: a -> [P.ArgDescr]
    parseArgs :: a -> ParsedOptionals -> P.ProcessorParser (Domains a)
    optionalParsers :: a -> [OptionalParser]
    parseInteractive :: a -> P.AnyProcessor -> IO (Domains a)


data Unit = Unit deriving (Typeable, Show)

data Arg k = Arg { name         :: String
                 , description  :: String
                 , defaultValue :: Domain k
                 , isOptional_  :: Bool}
             deriving Typeable 

infixr 5 :+:
data a :+: b = a :+: b deriving (Typeable, Show)

instance Arguments Unit where 
    type Domains Unit = ()

instance (Argument a) => Arguments (Arg a) where
    type Domains (Arg a) = Domain a

instance (Arguments a, Arguments b) => Arguments (a :+: b) where
    type Domains (a :+: b) = Domains a :+: Domains b

instance ParsableArguments Unit where
    parseArgs Unit _ = return ()
    optionalParsers Unit = []
    descriptions Unit = []
    parseInteractive _ _ = return ()

instance (ParsableArgument a, Show (Domain a), (Typeable (Domain a))) => ParsableArguments (Arg a) where
    parseArgs a opts | isOptional_ a = return $ fromMaybe (defaultValue a) lookupOpt 
                     | otherwise     = parseArg (Phantom :: Phantom a)
        where lookupOpt :: Maybe (Domain a)
              lookupOpt = do (SomeDomainElt e') <- Map.lookup (name a) opts
                             cast e'

    optionalParsers a | isOptional_ a = [ do _ <- string $ name a
                                             whiteSpace
                                             e <- parseArg (Phantom :: Phantom a)
                                             return (name a, SomeDomainElt e) ]
                      | otherwise     = []

    descriptions a = [P.ArgDescr { P.adIsOptional = isOptional_ a
                                 , P.adName       = name a
                                 , P.adDefault    = 
                                     if isOptional_ a 
                                     then Just $ showArg (Phantom :: Phantom a) (defaultValue a)
                                     else Nothing
                                 , P.adDescr      = description a
                                 , P.adSynopsis   = "[" ++ domainName (Phantom :: Phantom a)  ++ "]" }]

    parseInteractive a procs = 
        do putStrLn $ show (text "* '" <> text (name a) <> text "'"
                            $+$ nest 2 (descr $+$ text "" $+$ syn $+$ text ""))
           ask
      where syn = text "Synopsis:" <+> text (domainName phantom)
            descr = (U.paragraph (description a))
            ask | isOptional_ a = 
              do putStrLn $ show $ nest 2 $ U.paragraph ( "Use the default value '"
                                                         ++ showArg phantom (defaultValue a) 
                                                         ++"'? Enter 'yes' or 'no', default is 'yes':")
                 putStr "  > "
                 str <- getLine
                 if map toLower str == "no" 
                  then ask'
                  else return (defaultValue a)
                 | otherwise = ask'
            ask' = 
              do putStr "  > "
                 mres <- parseArgInteractive phantom procs
                 case mres of 
                   Nothing -> 
                       do putStrLn $ "Error parsing argument, expecting '" ++ (domainName phantom) ++ "'"
                          putStrLn "repeat input, or abort with Ctrl-c"
                          ask'
                   Just v -> return v

            phantom = Phantom :: Phantom a
                     
instance (ParsableArguments a, ParsableArguments b) => ParsableArguments (a :+: b) where
    parseArgs (a :+: b) opts = do e_a <- parseArgs a opts
                                  whiteSpace
                                  e_b <- parseArgs b opts
                                  return (e_a :+: e_b)

    optionalParsers (a :+: b) = optionalParsers a ++ optionalParsers b

    descriptions (a :+: b) = descriptions a ++ descriptions b

    parseInteractive (a :+: b) procs = 
     do pa <- parseInteractive a procs
        putStrLn ""
        pb <- parseInteractive b procs
        return (pa :+: pb)
        
-- operations on arguments

parseArguments :: ParsableArguments a => String -> a -> P.ProcessorParser (Domains a)
parseArguments hlp a = do opts <- Map.fromList `liftM` many (string ":" >> choice optparser)
                          parseArgs a opts <?> ("arguments for '" ++ hlp ++ "' of shape: \"" ++ synopsis a ++ "\"")
    where optparser = [ try $ do r <- p
                                 whiteSpace
                                 return r 
                        | p <- optionalParsers a]

synopsis :: ParsableArguments a => a -> String
synopsis a = ofList oSyn `app` ofList nSyn
    where oSyn = [ "[:" ++ P.adName d ++ " " ++ P.adSynopsis d ++ "]"| d <- opts]
          nSyn = [ P.adSynopsis d | d <- nonopts]
          (opts, nonopts) = partition P.adIsOptional (descriptions a)
          ofList l = concat $ intersperse " " l
          "" `app` n = n
          n `app` "" = n
          n `app` m  = n ++ " " ++ m

-- constructors and helpers

arg :: Arg a
arg = Arg { name         = "unspecified"
          , description  = []
          , defaultValue = error "no default argument given"
          , isOptional_  = False}

opt :: Arg a
opt = arg { isOptional_ = True }

optional :: Arg t -> String -> Domain t -> Arg t
optional tpe nm def = tpe { name = nm
                          , defaultValue = def
                          , isOptional_ = True}


unit :: Unit
unit = Unit


-- processor argument

