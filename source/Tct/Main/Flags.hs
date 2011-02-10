{-# LANGUAGE FlexibleInstances #-}
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

{-# LANGUAGE ExistentialQuantification #-}
module Tct.Main.Flags
 ( Flags(..)
 , AnswerType (..)
 , AT (..)
 , getFlags
 , helpMessage
 )
where 

import System
import List (intersperse, isPrefixOf)
import Char
import GHC.Conc (numCapabilities)
import Control.Monad.Instances()

-------------------------------------------------------------------------
-- flags

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

instance Read AnswerType where
  readsPrec _ s = [(AT rd (last s == '!'),"")]
    where rd | "dc"  `isPrefixOf` s = DC
             | "rc"  `isPrefixOf` s = RC
             | "irc" `isPrefixOf` s = IRC
             | "idc" `isPrefixOf` s = IDC
             | otherwise            = error "error reading answer type"

data Flags = Flags
  { input          :: FilePath
  , strategy       :: Maybe String
  , strategyFile   :: Maybe FilePath
  , proofOutput    :: Bool
  , time           :: Maybe Int
  , solver         :: Maybe String
  , answerType     :: Maybe AnswerType
  , listStrategies :: Maybe (Maybe String)
  , logFile        :: Maybe FilePath
  , showHelp       :: Bool
  , showVersion    :: Bool
  , performChecks  :: Bool
  } deriving (Eq, Show)

defaultFlags :: Flags
defaultFlags = Flags { strategy         = Nothing
                     , strategyFile     = Nothing
                     , input            = ""
                     , proofOutput      = True
                     , time             = Nothing
                     , answerType       = Nothing
                     , solver           = Nothing
                     , listStrategies   = Nothing
                     , logFile          = Nothing
                     , showHelp         = False
                     , showVersion      = False
                     , performChecks    = False}

data Option a
  = Option
  { long    :: String
  , short    :: String
  , meaning :: Arg (a -> a)
  , help    :: [String]
  }

options :: [Option Flags]
options =
  [ Option
    { long    = "timeout"
    , short    = "t"
    , meaning = (\n f -> f{ time = Just n }) <$> argNum
    , help    = [ "Maximum running time in seconds."
                ]
    }
  , Option
    { long    = "noproof"
    , short    = "p"
    , meaning = unit (\f -> f{ proofOutput = False })
    , help    = [ "Hide proof output."]
    }
  , Option
    { long    = "answer"
    , short    = "a"
    , meaning =  (\ n f -> f{ answerType = Just $ read n})  <$> argOption ["dc", "idc", "rc", "irc", "dc!", "idc!", "rc!", "irc!"]
    , help    = [ "Overwrite problem specification. Can be one of the following:"
                , " dc:  derivational complexity"
                , " idc: innermost derivational complexity"
                , " rc:  runtime complexity"
                , " irc: innermost runtime complexity"
                , "Add '!' at the end to throw an error if problem specification and given option conflict."]
    }
  , Option
    { long    = "minisat"
    , short    = "m"
    , meaning = (\n f -> f{ solver = Just n }) <$> argFile
    , help    = [ "Specify the path to the SatSolver executable."]
    }
  , Option
    { long    = "strategy"
    , short    = "s"
    , meaning = (\n f -> f{ strategy = Just n }) <$> argString
    , help    = [ "Specifies the strategy. For a list of strategies see '-l'."]
    }
  , Option
    { long    = "strategyfile"
    , short    = "S"
    , meaning = (\n f -> f{ strategyFile = Just n }) <$> argFile
    , help    = [ "Like '-s', but reads the strategy from the given file."]
    }
  , Option
    { long    = "strategies"
    , short   = "l"
    , meaning = (\ n f -> f{ listStrategies = Just n}) <$> argOptString
    , help    = [ "Prints a full list of strategies."]
    }
  , Option
    { long    = "logfile"
    , short    = "g"
    , meaning = (\n f -> f{ logFile = Just n }) <$> argFile
    , help    = [ "Enable logging. Logging output is sent to specified file."]
    }
  , Option
    { long    = "help"
    , short    = "h"
    , meaning = (\_ f -> f{ showHelp = True }) <$> argNone
    , help    = [ "Displays this help message."]
    }
  , Option
    { long    = "version"
    , short    = "v"
    , meaning = (\_ f -> f{ showVersion = True }) <$> argNone
    , help    = [ "Displays the version number."]
    }
  , Option
    { long    = "check"
    , short    = "c"
    , meaning = (\_ f -> f{ showVersion = True }) <$> argNone
    , help    = [ "Perform checks on the computed proof."]
    }

  ]

getFlags :: IO (Either [String] Flags)
getFlags = do as <- getArgs
              case parseFlags defaultFlags as of
                Right f  -> return $ Right f
                Left []  -> return $ Left ["Unknown error when parsing arguments."]
                Left err -> return $ Left ["Error when parsing arguments:"
                                         , show err
                                         , ""
                                         , "Try --help."]

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

argOptString :: Arg (Maybe String)
argOptString = MkArg ["<string>"] $ \xs ->
  case xs of
    x:xs' -> Right (Just x, xs')
    _     -> Right (Nothing, [])

            
-- argNums :: Arg [Int]
-- argNums = MkArg ["<nums>"] $ \xs ->
--   case xs of
--     []   -> Left ["expected a number list"]
--     x:xs' -> ((\a -> (a,xs')) `fmap`) . nums . groupBy (\x' y' -> isDigit x' == isDigit y') $ x ++ ","
--      where
--       nums []                = Right []
--       nums (n:",":ns)        = (read n :) `fmap` nums ns
--       nums (n:"..":m:",":ns) = ([read n .. read m] ++) `fmap` nums ns
--       nums _                 = Left ["number list garbled"]

argOption :: [String] -> Arg String
argOption as = MkArg [choices] $ \xs ->
  case xs of
    []   -> Left ["no argument given: expected one of " ++ choices]
    x:xs' -> ((\a -> (a,xs')) `fmap`) . elts $ x
      where
        elts x' | x' `elem` as = Right x'
                | otherwise   = Left ["unexpected option " ++ x'
                                    , "expecting one of " ++ choices]
  where choices = "<" ++ concat (intersperse " | " as) ++ ">"

-- argList :: [String] -> Arg [String]
-- argList as = MkArg ["<" ++ concat (intersperse " | " as) ++ ">*"] $ \xs ->
--   case xs of
--     []   -> Left ["expected a list"]
--     x:xs' -> ((\a -> (a,xs')) `fmap`) . elts $ x ++ ","
--      where
--       elts []              = Right []
--       elts s | w `elem` as = (w:) `fmap` elts r
--        where
--         w = takeWhile (/= ',') s
--         r = tail (dropWhile (/= ',') s)
    
--       elts _ = Left ["argument list garbled"]

parseFlags :: Flags -> [String] -> Either [String] Flags
parseFlags f []               = Right f
parseFlags f (('-':'-':x):xs) = parseFlags' f False x xs
parseFlags f (('-':x):xs)     = parseFlags' f True x xs
parseFlags f [x]              = Right f{input = x}
parseFlags _ xs                = Left xs

parseFlags' :: Flags -> Bool -> String -> [String] -> Either [String] Flags
parseFlags' f isShort x xs =
  case [ opt | opt <- options, x == (if isShort then short else long) opt ] of
    opt:_  -> case h xs of
                Left err      -> Left err
                Right (g,xs') -> parseFlags (g f) xs'
      where
      MkArg _ h = meaning opt
    []     -> Left ["Unrecognized option: '" 
                   ++ (if isShort then "-" else "--") ++ x ++ "'"]

-------------------------------------------------------------------------
-- help message

helpMessage :: [String]
helpMessage =
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
