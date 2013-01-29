{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_HADDOCK prune #-}

--------------------------------------------------------------------------------
-- | 
-- Module      :  Tct.Processor.Args
-- Copyright   :  (c) Martin Avanzini <martin.avanzini@uibk.ac.at>, 
--                Georg Moser <georg.moser@uibk.ac.at>, 
--                Andreas Schnabl <andreas.schnabl@uibk.ac.at>,
-- License     :  LGPL (see COPYING)
--
-- Maintainer  :  Martin Avanzini <martin.avanzini@uibk.ac.at>
-- Stability   :  unstable
-- Portability :  unportable      
-- 
-- This module implements processor arguments.
--------------------------------------------------------------------------------   

module Tct.Processor.Args 
       (
         Argument (..)
       , ParsableArgument (..)
         
       -- * Argument Descriptions
       , Arg (..)
       , arg  
       , opt
       , optional
         
       , Unit (..)
       , (:+:)(..)
       -- hidden         
       , Arguments (..)
       , ParsableArguments (..)
       , Phantom (..)
       , parseArguments
       , synopsis
       -- , withLineBuffering
       , InteractiveParser (..)
       , defaultIP
       ) where

import qualified Tct.Processor as P
import qualified Tct.Utils.Xml as Xml


import qualified Tct.Utils.Ask as Ask
import Tct.Processor.Parse
import Text.Parsec.Prim
import Text.Parsec.Combinator hiding (optional)
import Text.Parsec.Char
import qualified Data.Map as Map
import Data.List (partition, intersperse)
import Data.Typeable (cast, Typeable)
import Control.Monad (liftM)
import Data.Maybe (fromMaybe)
import Text.PrettyPrint.HughesPJ

import qualified Termlib.Utils as U
-- single argument
data Phantom k = Phantom

-- | Instances of this class can be used as processor arguments.
-- Parsers are specified separately in the class 'ParsableArgument'.
-- The associated type 'Domain a' reflects the type of the Haskell values. 
-- This type does not necessarily need to coincide with 'a', but for simple
-- instances like 'Bool' it does, i.e. 'Domain Bool == Bool'.
class Argument a where
    type Domain a 
    -- | Short string describing the argument type.    
    domainName :: Phantom a -> String 
    -- | Pretty printer of arguments.    
    showArg :: Phantom a -> Domain a -> String


data InteractiveParser a = IP { ipCompletions :: [String] 
                              , ipSynopsis :: Doc
                              , ipParse :: String -> IO (Either Doc (Domain a))}


defaultIP :: ParsableArgument a => [String] -> Phantom a -> P.AnyProcessor -> InteractiveParser a
defaultIP completions pa procs = 
  IP { ipCompletions = completions
     , ipSynopsis = U.paragraph $ domainName pa
     , ipParse = return . p }
  where 
    p str = case fromString (parseArg pa) procs "argument" str of 
              Right a -> Right a
              Left err -> Left $ U.paragraph $ show err

-- | Instances of this class additionally provide parsers for arguments.
class (Argument a) => ParsableArgument a where
    parseArg :: Phantom a -> P.ProcessorParser (Domain a)
    interactiveParser :: Phantom a -> P.AnyProcessor -> InteractiveParser a
    interactiveParser = defaultIP []
        
data SomeDomainElt = forall a. (Show a, Typeable a) => SomeDomainElt a deriving (Typeable)
instance Show SomeDomainElt where show (SomeDomainElt e) = show e
type ParsedOptionals = Map.Map String SomeDomainElt
type OptionalParser = P.ProcessorParser (String, SomeDomainElt)

class Arguments a where
    type Domains a 
    toXml :: a -> Domains a -> [Xml.XmlContent]

class Arguments a => ParsableArguments a where
    descriptions :: a -> [P.ArgDescr]
    parseArgs :: a -> ParsedOptionals -> P.ProcessorParser (Domains a)
    optionalParsers :: a -> [OptionalParser]
    parseInteractive :: a -> P.AnyProcessor -> IO (Domains a)


-- | Unit represents the empty argument list.
data Unit = Unit deriving (Typeable, Show)

-- | This datatype captures the description of a single argument. 
data Arg t = Arg { name         :: String -- ^ The name of the argument.
                 , description  :: String -- ^ Optional description for the argument.
                 , defaultValue :: Domain t -- ^ A possible default value, if the argument is optional.
                 , isOptional_  :: Bool -- ^ Indicates wether the argument is optional.
                 }
             deriving Typeable 

infixr 5 :+:

-- | This operator constructs /tuples/ of arguments.
data a :+: b = a :+: b deriving (Typeable, Show)

instance Arguments Unit where 
    type Domains Unit = ()
    toXml _ _ = []

instance (Argument a) => Arguments (Arg a) where
    type Domains (Arg a) = Domain a
    toXml (a :: Arg a) d = 
      [Xml.elt "argument" []
        [ Xml.elt "name" [] [Xml.text $ name a]
        , Xml.elt "description" [] [Xml.text $ name a]
        , Xml.elt "value" [] [Xml.text $ showArg (Phantom :: Phantom a) d]]]

instance (Arguments a, Arguments b) => Arguments (a :+: b) where
    type Domains (a :+: b) = Domains a :+: Domains b
    toXml (a :+: b) (da :+: db) = toXml a da ++ toXml b db
    
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
                                 , P.adSynopsis   = domainName (Phantom :: Phantom a) }]

    parseInteractive pa procs = do 
        putStrLn $ show $ text "- Argument '" <> text (name pa) <> text "' (type :h for help)"
        ask
      where 
         descr = U.paragraph (description pa)

         prompt 
           | isOptional_ pa = "[" ++ showArg phantom (defaultValue pa) ++ "] > "
           | otherwise      = "> "

         ip = interactiveParser phantom procs

         phantom = Phantom :: Phantom a

         trim [] = []
         trim (' ':xs) = case trim xs of 
                           [] -> []
                           xs' -> ' ':xs'
         trim (x:xs) = x:trim xs
                  
         ask = do 
           mstr <- Ask.ask prompt (ipCompletions ip ++ [":h"]) Just
           process $ trim `liftM` mstr

         process Nothing = putHelp >> ask
         process (Just "") | isOptional_ pa = return $ defaultValue pa
         process (Just ":h") = putHelp >> ask 

         process (Just str) = do 
           res <- ipParse ip str
           case res of 
             Left _ -> putStrLn "" >> putStrLn ("Error parsing argument. Type ':h' for help.") >> ask
             Right a  -> return a 

         putHelp = 
           putStrLn $ show $ 
           nest 2 $ 
           text ""
           $+$ descr 
           $+$ text ""
           $+$ text "Synopsis:" <+> ipSynopsis ip
           $+$ text ""

  
                     
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

-- | Constructor for description of arguments of type @t@.
arg :: Arg t
arg = 
  Arg { name         = "unspecified"
      , description  = []
      , defaultValue = error "no default argument given"
      , isOptional_  = False}

opt :: Arg t
opt = 
  Arg { name         = "unspecified"
      , description  = []
      , defaultValue = error "no default argument given"
      , isOptional_  = True}


-- | Constructor for description of optional arguments of type @t@.
-- The following describes an optional argument /dimension/ with default
-- value /2/.
--
-- >>> optional naturalArg "dimension" 2
--
optional :: Arg t -> String -> Domain t -> Arg t
optional tpe nm def = 
  tpe { name = nm
      , defaultValue = def
      , isOptional_ = True}


-- withLineBuffering :: IO b -> IO b
-- withLineBuffering io = do 
--   bm <- hGetBuffering stdin
--   hSetBuffering stdin LineBuffering
--   io `C.finally` hSetBuffering stdin bm
 
 