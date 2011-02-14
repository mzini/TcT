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
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE FlexibleInstances #-}
module Tct 
    ( Config (..)
    , TCTError (..)
    , TCTWarning (..)
    , defaultConfig
    , run)
    -- , readProblem
    -- , check
    -- , putProof)
where 

import Control.Monad.Error
import Control.Exception (evaluate)
import Control.Monad.RWS.Lazy
import Data.Typeable 
import System.Directory
import System.IO
import System.FilePath ((</>))
import Text.PrettyPrint.HughesPJ
import qualified Control.Exception as C

import Termlib.Problem (Problem, onProblem, standardProblem, dpProblem, relativeProblem, wellFormed)
import qualified Termlib.Problem as Prob
import Termlib.Utils (PrettyPrintable (..), paragraph)
import qualified Termlib.Problem as Prob
import qualified Termlib.Problem.ParseErrors as ProblemPEs
import qualified Termlib.Problem.Parser as ProblemParser
import qualified Termlib.Trs as Trs

import System
import List (intersperse, isPrefixOf)
import Char
import GHC.Conc (numCapabilities)
import Control.Monad.Instances()

import Tct.Main.Flags
import Tct.Processor
import Tct.Processor.LoggingSolver
import qualified Tct.Main.Version as Version
import qualified Tct.Processor.Timeout as Timeout
import qualified Tct.Methods as Methods
import Tct.Methods (Nat (..), Size (..))

----------------------------------------------------------------------
-- Config 

type ErroneousIO a = ErrorT TCTError IO a

data Config = Config { processor         :: Problem -> AnyProcessor -> ErroneousIO SomeInstance
                     , processors        :: AnyProcessor
                     , problemFile       :: String
                     , getSolver         :: ErroneousIO SatSolver
                     , putProof          :: Proof SomeProcessor -> IO ()
                     , putError          :: TCTError -> IO ()
                     , putWarning        :: TCTWarning -> IO ()
                     , configDir         :: ErroneousIO FilePath
                     , errorMsg          :: [String]
                     , version           :: String

                     , timeout           :: Maybe Int
                     , answerType        :: Maybe AnswerType
                     , listStrategies    :: Maybe (Maybe String)
                     , logFile           :: Maybe FilePath
                     , showProof         :: Bool
                     , showHelp          :: Bool
                     , showVersion       :: Bool
                     , performChecks     :: Bool }


options :: Options Config
options =
  [ Option
    { long    = "timeout"
    , short    = "t"
    , meaning = (\n f -> f{ timeout = Just n }) <$> argNum
    , help    = [ "Maximum running time in seconds."] }
  , Option
    { long    = "noproof"
    , short    = "p"
    , meaning = unit (\f -> f{ showProof = False })
    , help    = [ "Hide proof output."] }
  , Option
    { long    = "answer"
    , short    = "a"
    , meaning =  (\ n f -> f{ answerType = Just n})  <$> argAT
    , help    = [ "Overwrite problem specification. Can be one of the following:"
                , " dc:  derivational complexity"
                , " idc: innermost derivational complexity"
                , " rc:  runtime complexity"
                , " irc: innermost runtime complexity"
                , "Add '!' at the end to throw an error if problem specification and given option conflict."] }
  , Option
    { long    = "minisat"
    , short    = "m"
    , meaning = (\n f -> f{ getSolver = findSolver MiniSat n }) <$> argFile
    , help    = [ "Specify the path to the minisat SAT-solver executable."] }
  , Option
    { long    = "strategy"
    , short    = "s"
    , meaning = (\n f -> f{ processor = const $ processorFromString n }) <$> argString
    , help    = [ "Specifies the strategy. For a list of strategies see '-l'."]
    }
  , Option
    { long    = "strategyfile"
    , short    = "S"
    , meaning = (\n f -> f{ processor = const $ processorFromFile n }) <$> argFile
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
    , meaning = (\_ f -> f{ performChecks = True }) <$> argNone
    , help    = [ "Perform checks on the computed proof."]
    }

  ]

defaultConfig :: Config
defaultConfig = Config { processor       = defaultProcessor
                       , processors      = Methods.builtInProcessors
                       , problemFile     = ""
                       , getSolver       = getDefaultSolver
                       , putProof        = liftIO . putStrLn . show . pprint
                       , putError        = liftIO . hPutStrLn stderr . show . pprint 
                       , putWarning      = liftIO . hPutStrLn stderr . show . pprint
                       , configDir       = do home <- liftIO $ getHomeDirectory 
                                              return $ home </> ".tct"
                       , errorMsg        = []
                       , version         = Version.version
                                           
                       , timeout         = Nothing
                       , answerType      = Nothing
                       , listStrategies  = Nothing
                       , logFile         = Nothing
                       , showProof       = True
                       , showHelp        = False
                       , showVersion     = False
                       , performChecks   = False}

defaultProcessor :: Problem -> AnyProcessor -> ErroneousIO SomeInstance
defaultProcessor prob _ = return $ case Prob.startTerms prob of 
                                     Prob.TermAlgebra -> SomeInstance $ matrices Methods.Triangular
                                     _                -> SomeInstance $ wdg (matrices Methods.Constructor)
    where matrices kind = Methods.fastest [ Methods.matrix kind (Nat dim) (Bits 3) (Just $ Nat 4) True | dim <- [1, 2, 3] ]
          wdg           = Methods.wdg Methods.Edg True Methods.Default (Nat 2) (Bits 3) (Just $ Nat 4) True False True

findSolver :: (String -> SatSolver) -> String -> ErroneousIO SatSolver
findSolver mk nm = do mr <- liftIO $ findExecutable nm
                      case mr of 
                        Just s  -> return $ mk s
                        Nothing -> throwError $ SatSolverMissing $ "Cannot find sat-solver executable " ++ nm

run :: Flags -> Config -> IO (Maybe TCTError, [TCTWarning])
run flg cfg = do let rostate = TCTROState { config    = cfg
                                          , flags     = flg}
                 mk `liftM` evalRWST (runErrorT (tct $ readProblem >>= check >>= putProof)) rostate TCTState 
    where mk (Left e,r) = (Just e, r)
          mk (_     ,r) = (Nothing, r)
check :: Problem -> TCT (Proof SomeProcessor)
check prob = do fn <- askConfig process
                getProc <- askConfig getProcessor
                proc <- getProc prob
                fn proc prob


processorFromString :: String -> AnyProcessor -> ErroneousIO SomeInstance
processorFromString str allProcessors = case fromString allProcessors str of 
                                          Left err    -> throwError $ StrategyParseError $ show err
                                          Right proc' -> return $ SomeInstance proc'

processorFromFile :: FilePath -> AnyProcessor -> ErroneousIO SomeInstance
processorFromFile fn allProcessors =  do str <- (liftIO $ readFile fn `catch` const (return ""))
                                         case str of 
                                           ""  -> throwError (strMsg $ "cannot read strategy from file " ++ fn)
                                           _   -> processorFromString str allProcessors


run :: Config -> IO (Maybe TCTError, [TCTWarning])
run = undefined
----------------------------------------------------------------------
-- Warning
data TCTWarning = ProblemParseWarning ProblemPEs.ParseWarning deriving Show

pprintErr :: String -> Doc -> Doc
pprintErr m e = nest 1 $ paragraph m <> text ":" $$ (nest 2 e)

instance PrettyPrintable TCTWarning where
  pprint (ProblemParseWarning w) = pprintErr "Warning when parsing problem" $ pprint w

instance PrettyPrintable [TCTWarning] where
  pprint [] = empty
  pprint ws = fsep [pprint w | w <- ws]


----------------------------------------------------------------------
-- TCT error
data TCTError = StrategyParseError String
              | ProblemParseError ProblemPEs.ParseError
              | ProblemUnknownFileError String
              | ProblemNotWellformed Problem
              | AnswerTypeMisMatch
              | ProblemMissingError 
              | SatSolverMissing String
              | SomeExceptionRaised C.SomeException
              | FlagsParseError [String]
              | UnknownError String deriving (Typeable)

instance PrettyPrintable TCTError where 
  pprint (StrategyParseError s)      = pprintErr "Error when parsing strategy" $ text s
  pprint (ProblemParseError e)       = pprintErr "Error when parsing problem" $ pprint e
  pprint ProblemMissingError         = text "No problem supplied"
  pprint (UnknownError s)            = pprintErr "Unknown error" $ text s
  pprint AnswerTypeMisMatch          = text "Answer type does not match problem type"
  pprint (ProblemUnknownFileError s) = pprintErr "Don't know how to parse file" $ quotes (text s) 
  pprint (ProblemNotWellformed prob) = pprintErr "The problem does not contain well-formed TRSs" $ pprint prob
  pprint (SatSolverMissing e)        = pprintErr "There is a problem with the MiniSat executable. Please specify appropriately with flag -minisat. Reason was" $ text e
  pprint (SomeExceptionRaised e)     = pprintErr "The following exception was raised during computation" (text $ show e)
  pprint (FlagsParseError strs)      = pprintErr "Error when parsing arguments" $ vcat [text t | t <- strs] $$ text "Try --help."

instance Show TCTError where show = show . pprint

instance Error TCTError where strMsg = UnknownError

----------------------------------------------------------------------
-- TCT monad

data TCTState = TCTState
data TCTROState = TCTROState { config    :: Config }

newtype TCT r = TCT { 
    tct :: ErrorT TCTError (RWST TCTROState [TCTWarning] TCTState IO) r
  } deriving (Monad, Functor, MonadIO, MonadError TCTError, MonadReader TCTROState)

