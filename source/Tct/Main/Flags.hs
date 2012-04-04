{-# LANGUAGE FlexibleInstances #-}
{-# OPTIONS_HADDOCK hide #-}

--------------------------------------------------------------------------------
-- | 
-- Module      :  Tct.Main.Debug
-- Copyright   :  (c) Koen Claessen, Niklas Sorensson
--
-- Maintainer  :  Martin Avanzini <martin.avanzini@uibk.ac.at>
-- Stability   :  unstable
-- Portability :  unportable      
-- 
-- Parsing of Flags, copied from Paradox/Equinox with minor modifications.
--------------------------------------------------------------------------------   

{-
Paradox/Equinox -- Copyright (c) 2003-2007, Koen Claessen, Niklas Sorensson

Permission is hereby granted, free of charge, to any person obtaining a
copy of this software and associated documentation files (the
"Software"), to deal in the Software without restriction, including
without limitation the rights to use, copy, modify, merge, publish,
distribute, sublicense, and/or sell copies of the Software, and to
permit persons to whom the Software is furnished to do so, subject to
the following conditions:

The above copyright notice and this permission notice shall be included
in all copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS
OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE
LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION
OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION
WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
-}



module Tct.Main.Flags
 ( AnswerType (..)
 , AT (..)
 , makeHelpMessage
 , parseOptions
 , Options
 , Option (..)
 , (<$>)
 , args
 , unit
 , argNum 
 , argAT
 , argFile
 , argString
 , argNone
 , argOption
 , argOptString
 )
where 

import Data.Char
import Data.List (intersperse, isPrefixOf)
import GHC.Conc (numCapabilities)
import Control.Monad.Instances()

-------------------------------------------------------------------------
-- answer type 

data AT = DC | IDC | RC | IRC deriving (Eq,Ord)

data AnswerType = AT { atype :: AT
                     , isStrict :: Bool
                     } deriving (Eq)

instance Show AnswerType where
  show (AT a s) = toStr a ++ if s then "!" else ""
    where toStr DC  = "dc"
          toStr IDC = "idc"
          toStr RC  = "rc"
          toStr IRC = "irc"

-------------------------------------------------------------------------
-- flags

data Option a = Option { long    :: String
                       , short   :: String
                       , meaning :: Arg (a -> a)
                       , help    :: [String] }

-------------------------------------------------------------------------
-- arg

data Arg a = MkArg [String] ([String] -> Either [String] (a, [String]))

unit :: a -> Arg a
unit x = MkArg [] (\s -> Right (x,s))

(<*>) :: Arg (a -> b) -> Arg a -> Arg b
MkArg fs f <*> MkArg xs x =
  MkArg (fs++xs) (\s ->
    case f s of
      Left err     -> Left err
      Right (h,s') -> case x s' of
                        Left err      -> Left err
                        Right (a,s'') -> Right (h a,s'')
  )

(<$>) :: (a -> b) -> Arg a -> Arg b
f <$> x = unit f <*> x

args :: Arg a -> [String]
args (MkArg as _) = as

-------------------------------------------------------------------------
-- parsers

argNone :: Arg ()
argNone = MkArg [] $ \xs -> Right ((),xs)

argNum :: (Read a, Num a) => Arg a
argNum = MkArg ["<num>"] $ \xs ->
  case xs of
    x:xs'       | all isDigit x -> Right (read x, xs')
    ('-':x):xs' | all isDigit x -> Right (-read x, xs')
    _                          -> Left ["expected a number"]
      
argFile :: Arg FilePath
argFile = MkArg ["<file>"] $ \xs ->
  case xs of
    x:xs' -> Right (x, xs')
    _     -> Left ["expected a file"]

argString :: Arg String
argString = MkArg ["<string>"] $ \xs ->
  case xs of
    x:xs' -> Right (x, xs')
    _     -> Left ["expected a string"]

argAT :: Arg AnswerType
argAT = mk <$> argOption (ats ++ [a ++ "!" | a <- ats])
    where ats = [ "dc", "rc", "irc", "idc" ]
          mk s = AT { atype = rd s, isStrict = last s == '!'}
          rd s | "dc"  `isPrefixOf` s = DC
               | "rc"  `isPrefixOf` s = RC
               | "irc" `isPrefixOf` s = IRC
               | "idc" `isPrefixOf` s = IDC
               | otherwise            = error "Cannot happen: Bug in Tct.Main.Flags.argOption"

argOptString :: Arg (Maybe String)
argOptString = MkArg ["<string>"] $ \xs ->
  case xs of
    x:xs' -> Right (Just x, xs')
    _     -> Right (Nothing, [])

argOption :: [String] -> Arg String
argOption as = MkArg [choices] $ \xs ->
  case xs of
    []   -> Left ["no argument given: expected one of " ++ choices]
    x:xs' -> ((\a -> (a,xs')) `fmap`) . elts $ x
      where
        elts x' | x' `elem` as = Right x'
                | otherwise   = Left ["unexpected option " ++ x'
                                    , "expecting one of " ++ choices]
  where choices = "< " ++ concat (intersperse " | " as) ++ " >"

type Options a = [Option a]

----------------------------------------------------------------------
--- Options

makeHelpMessage :: Options a -> [String]
makeHelpMessage options =
  [ "Usage: tct <option>* <file>"
  , ""
  , "<file> refers to a problem specification as TPDB .xml or .trs file."
  , "<option> can be any of the following:"
  ] ++
  concat
  [ [ ""
    , "  -" ++ short opt ++ ", --" ++ long opt ++ " " ++ unwords (args (meaning opt))
    ] ++ map ("    "++) (help opt)
  | opt <- options
  ] ++
   ["We are running on " ++ show numCapabilities ++ " cores."]


parseOptions :: Options a -> (FilePath -> a -> a) -> a -> [String] -> Either [String] a
parseOptions _       _        f []               = Right f
parseOptions options setInput f (('-':'-':x):xs) = parseOptions' options setInput f False x xs
parseOptions options setInput f (('-':x):xs)     = parseOptions' options setInput f True x xs
parseOptions _       setInput f [x]              = Right $ setInput x f
parseOptions _       _        _ xs               = Left xs

parseOptions' :: Options a -> (FilePath -> a -> a) -> a -> Bool -> String -> [String] -> Either [String] a
parseOptions' options setInput f isShort x xs =
  case [ opt | opt <- options, x == (if isShort then short else long) opt ] of
    opt:_  -> case h xs of
                Left err      -> Left err
                Right (g,xs') -> parseOptions options setInput (g f) xs'
      where MkArg _ h = meaning opt
    []     -> Left ["Unrecognized option: '" 
                   ++ (if isShort then "-" else "--") ++ x ++ "'"]