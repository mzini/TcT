{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE TypeSynonymInstances #-}

--------------------------------------------------------------------------------
-- | 
-- Module      :  Tct.Processor.Args.Instances
-- Copyright   :  (c) Martin Avanzini <martin.avanzini@uibk.ac.at>, 
--                Georg Moser <georg.moser@uibk.ac.at>, 
--                Andreas Schnabl <andreas.schnabl@uibk.ac.at>,
-- License     :  LGPL (see COPYING)
--
-- Maintainer  :  Martin Avanzini <martin.avanzini@uibk.ac.at>
-- Stability   :  unstable
-- Portability :  unportable      
-- 
-- This module defines various instances of processor arguments.
--------------------------------------------------------------------------------   

module Tct.Processor.Args.Instances 
       ( Proc (..)
       , Processor
       , Assoc (..)
       , AssocArgument (..)
       , EnumOf (..)
       , Nat (..)
       , nat
       , natToInt
       -- * Constructors for Arguments
       , naturalArg
       , boolArg
       , maybeArg
       , listArg         
       , processorArg
       , EnumArg
       , AssocArg
       ) 
       where

import Data.Typeable
import Control.Monad (liftM)
import Text.Parsec.Combinator (choice)
import Text.Parsec.Char (string)
import Data.List (intersperse, sortBy)
import Text.Parsec.Prim (many, try, (<|>))
import Tct.Processor.Parse hiding (natural, bool)
import qualified Tct.Processor.Parse as Parse
import Tct.Processor.Args
import Termlib.Utils (PrettyPrintable (..))
import Text.PrettyPrint.HughesPJ
import qualified Tct.Processor as P
import qualified Data.List as L


-- * Primitives
newtype Nat = Nat Int deriving (Typeable, Eq, Ord, Show, Num, Enum)

nat :: Int -> Nat
nat i | i < 0 = error "nat received negative integer"
      | otherwise = Nat i

natToInt :: Nat -> Int
natToInt (Nat i) = i

instance Argument Nat where
    type Domain Nat = Nat

    domainName Phantom = "<nat>"
    showArg _ (Nat i) = show i 

instance PrettyPrintable Nat where
    pprint (Nat i) = text (show i)

instance ParsableArgument Nat where
    parseArg Phantom = Nat `liftM` Parse.natural

instance Argument Bool where
    type Domain Bool = Bool
    domainName Phantom = "On|Off"
    showArg _ True = "On"
    showArg _ False = "Off"

instance ParsableArgument Bool where
    parseArg Phantom = Parse.bool
    interactiveParser = defaultIP ["On", "Off"]
      
-- * Compound

instance Argument a => Argument [a] where 
    type Domain [a] = [Domain a]
    domainName Phantom =  domainName (Phantom :: Phantom a) ++ "..."
    showArg _ as = "[" ++ concat (L.intersperse ", " [showArg (Phantom :: Phantom a) a | a <- as]) ++ "]"

instance Argument a => Argument (Maybe a) where 
    type Domain (Maybe a) = Maybe (Domain a)
    domainName Phantom = domainName (Phantom :: Phantom a) ++ "|none"      
    showArg _ (Just a)   = showArg (Phantom :: Phantom a) a
    showArg _ Nothing    = "none"

instance ParsableArgument a => ParsableArgument (Maybe a) where 
    parseArg Phantom = try (string "none" >> return Nothing)
                       <|> Just `liftM` parseArg (Phantom :: Phantom a)
    interactiveParser (_ :: Phantom (Maybe a)) procs = 
      IP { ipCompletions = "none" : ipCompletions ip
         , ipSynopsis = text "none|" <> ipSynopsis ip
         , ipParse = prs }
              
      where pa = Phantom :: Phantom a 
            ip = interactiveParser pa procs
            prs "none" = return $ Right Nothing
            prs str = do 
              res <- ipParse ip str
              return $ case res of 
                         Left err -> Left err
                         Right a -> Right (Just a)
              
instance ParsableArgument a => ParsableArgument [a] where
    parseArg Phantom = many p 
        where p :: P.ProcessorParser (Domain a)
              p = do r <- parseArg (Phantom :: Phantom a)
                     try whiteSpace <|> return ()
                     return r

newtype EnumOf a = EnumOf a    

domainNameList :: [String] -> String
domainNameList l = concat $ intersperse "|" [ e | e <- l ]

parseArgAssoc :: [(String,e)] -> P.ProcessorParser e
parseArgAssoc  l = choice [ try $ pa n e | (n,e) <- l]
        where pa n e = do _ <- string n
                          return e

instance (Typeable a, Show a, Enum a, Bounded a) => Argument (EnumOf a) where
    type Domain (EnumOf a) = a
    domainName Phantom = domainNameList [show e | e <- [(minBound :: a) .. maxBound]]
    showArg _ a = show a

instance (Typeable a, Show a, Enum a, Bounded a) => ParsableArgument (EnumOf a) where
    parseArg Phantom = parseArgAssoc [(show e, e) | e <- [(minBound :: a) .. maxBound]]
    interactiveParser = defaultIP options
      where options = [show e | e <- [(minBound :: a) .. maxBound]]

-- | Instances of this class can be parsed by means of the
-- defined method 'assoc'. 
class AssocArgument a where 
    -- | The resulting list associates names to elements, and should be finite.
    -- An element is parsed by parsing its name.
    assoc :: Phantom a -> [(String, a)]

newtype Assoc a = Assoc a

instance (Show a, AssocArgument a) => Argument (Assoc a) where
    type Domain (Assoc a) = a
    domainName _ = domainNameList [ s | (s,_) <- assoc (Phantom :: Phantom a)]
    showArg _ a  = show a

instance (Show a, AssocArgument a) => ParsableArgument (Assoc a) where
    parseArg _ = parseArgAssoc $ assoc (Phantom :: Phantom a)


data Proc a = Proc a

instance (P.Processor a) => Argument (Proc a) where
    type Domain (Proc a) = P.InstanceOf a
    domainName _ = "<processor>"
    showArg _ a    = "<processor " ++ P.instanceName a ++ ">"

type Processor = Proc P.AnyProcessor

instance ParsableArgument Processor where
    parseArg _ = P.parseAnyProcessor
    interactiveParser _ procs = 
      IP { ipCompletions = [ n | (n, _) <- procLst]
         , ipSynopsis = text "<processor>"
         , ipParse = prs } 
      
      where 
        procLst = [(P.name p, p) | p <- sortBy compareName $ P.toProcessorList procs]
          where compareName p1 p2 = P.name p1 `compare` P.name p2
        prs n = 
          case lookup n procLst of 
            Nothing -> return $ Left $ text $ "Processor '" ++ n ++ "' not known"
            Just proc -> do 
              parsed <- P.parseFromArgsInteractive proc procs
              return $ Right $ P.liftOOI parsed


-- argument types

-- | Natural argument  
naturalArg :: Arg Nat
naturalArg = arg

-- | Boolean argument, which is parsed as either /On/ or /Off/.
boolArg :: Arg Bool
boolArg = arg


-- | Argument, that additionally parses as 'none'.
maybeArg :: Arg a -> Arg (Maybe a)
maybeArg a = a {defaultValue = Just $ defaultValue a}


-- | A list of arguments. 
listArg :: Arg a -> Arg [a]
listArg a = a {defaultValue = [defaultValue a]}


-- | Construct an argument from an associated list, by declaring 
-- a datatype an instance of 'AssocArgument'. 
-- Use as follows:
-- 
-- >>> instance AssocArgument MyType where 
--      assoc _ = [("nameA", valueA), ("nameB", valueB)...]
-- 
-- Then one can use a declaration
--
-- >>> arg :: AssocArg MyType
--
-- which will parse /valueA/ as /nameA/, /valueB/ as /nameB/, and so on. 

type AssocArg a = Arg (Assoc a)

-- | Processor argument
processorArg :: Arg Processor
processorArg = arg

-- | This can be used to lift instances of 'Typeable', 'Show', 'Enum' and 'Bounded' to arguments.
-- Suppose you have a datatype like the following.
-- 
-- >>> data MyType = A | B | C deriving (Typeable, Show, Enum, Bounded)
-- 
-- An argument description for an element of type @MyType@ is then given by 
--
-- >>> arg :: EnumArg MyType
-- 
type EnumArg a = Arg (EnumOf a)

