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
    , runTct
    , parseArguments
    , runErroneous)
where 

import Control.Monad.Error
import Control.Monad.RWS.Lazy
import Data.Typeable 
import System.Directory
import System.IO
import System.FilePath ((</>))
import Text.PrettyPrint.HughesPJ
import qualified Control.Exception as C
import Data.Maybe (isJust)
import Data.List (sortBy)
import Text.Regex (mkRegex, matchRegex)

import Termlib.Problem (Problem, onProblem, standardProblem, dpProblem, relativeProblem, wellFormed)
import qualified Termlib.Problem as Prob
import Termlib.Utils (PrettyPrintable (..), paragraph)
import qualified Termlib.Problem.ParseErrors as ProblemPEs
import qualified Termlib.Problem.Parser as ProblemParser
import qualified Termlib.Trs as Trs

import System
import Control.Monad.Instances()

import Tct.Main.Flags
import Tct.Processor
import Tct.Processor.LoggingSolver
import qualified Tct.Main.Version as Version
import qualified Tct.Methods as Methods
import Tct.Methods (Nat (..), Size (..))


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
  pprint (FlagsParseError strs)      = pprintErr "Error when parsing arguments" $ vcat [text t | t <- strs] $$ text "" $$ text "Try --help."

instance Show TCTError where show = show . pprint

instance Error TCTError where strMsg = UnknownError

type ErroneousIO = ErrorT TCTError IO

runErroneous :: ErroneousIO a -> IO (Either TCTError a)
runErroneous = runErrorT


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
--- Config

data Config = Config { processor         :: Problem -> AnyProcessor -> ErroneousIO (InstanceOf SomeProcessor)
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



defaultConfig :: Config
defaultConfig = Config { processor       = defaultProcessor
                       , processors      = Methods.builtInProcessors
                       , problemFile     = ""
                       , getSolver       = getDefaultSolver
                       , putProof        = hPutPretty stdout
                       , putError        = \ e -> hPutStrLn stderr "ERROR" >> hPutStrLn stderr "" >> hPutPretty stderr e
                       , putWarning      = hPutPretty stderr
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

  where defaultProcessor prob _ = return $ case Prob.startTerms prob of 
          Prob.TermAlgebra -> someInstance $ matrices Methods.Triangular
          _                -> someInstance $ wdg (matrices Methods.Constructor)
        matrices kind = Methods.fastest [ Methods.matrix kind (Nat dim) (Bits 3) (Just $ Nat 4) True | dim <- [1, 2, 3] ]
        wdg           = Methods.wdg Methods.Edg True Methods.Default (Nat 2) (Bits 3) (Just $ Nat 4) True False True
        getDefaultSolver = findSatSolver MiniSat "minisat" `catchError` (const $ findSatSolver MiniSat "minisat2")


findSatSolver :: (String -> SatSolver) -> String -> ErroneousIO SatSolver
findSatSolver mk nm = do fn <- findExe 
                         checkExe fn
                         return $ mk fn
  where findExe :: ErroneousIO FilePath 
        findExe = do mr <- liftIO $ findExecutable nm
                     case mr of 
                       Just s  -> return s 
                       Nothing -> err $ "Cannot find sat-solver executable " ++ nm
        checkExe :: FilePath -> ErroneousIO ()
        checkExe fn = do exists <- liftIO $ doesFileExist fn
                         unless exists (err $ "Given filename " ++ fn ++ " is not executable")
                         p <- liftIO $ getPermissions fn
                         unless (executable p) (err $ "Given executable " ++ fn ++ " does not exist")
        err = throwError .  SatSolverMissing
        
processorFromString :: String -> AnyProcessor -> ErroneousIO (InstanceOf SomeProcessor)
processorFromString str allProcessors = case fromString allProcessors str of 
                                          Left err    -> throwError $ StrategyParseError $ show err
                                          Right proc' -> return proc'

processorFromFile :: FilePath -> AnyProcessor -> ErroneousIO (InstanceOf SomeProcessor)
processorFromFile fn allProcessors =  do str <- (liftIO $ readFile fn `catch` const (return ""))
                                         case str of 
                                           ""  -> throwError (strMsg $ "cannot read strategy from file " ++ fn)
                                           _   -> processorFromString str allProcessors


hPutPretty :: PrettyPrintable a => Handle -> a -> IO ()
hPutPretty handle = liftIO . hPutStrLn handle . show . pprint 

----------------------------------------------------------------------
--- Options
  
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
    , meaning = (\n f -> f{ getSolver = findSatSolver MiniSat n }) <$> argFile
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


----------------------------------------------------------------------
-- TCT monad

data TCTState = TCTState
data TCTROState = TCTROState { config    :: Config }

newtype TCT r = TCT { 
    tct :: RWST TCTROState [TCTWarning] TCTState ErroneousIO r
    } deriving (Monad, Functor, MonadIO, MonadError TCTError, MonadReader TCTROState, MonadWriter [TCTWarning])


fromConfig :: (Config -> c) -> TCT c
fromConfig f = (f . config) `liftM` ask

warn :: TCTWarning -> TCT ()
warn w = tell [w]

liftEIO :: ErroneousIO a -> TCT a
liftEIO m = do me <- liftIO $ runErroneous m
               case me of 
                 Left e -> throwError e
                 Right e -> return e
                 
putPretty :: (MonadIO m) => Doc -> m ()
putPretty a = liftIO $ putStrLn $ show a

runTct :: Config -> ErroneousIO [TCTWarning]
runTct cfg = snd `liftM` evalRWST (tct m) TCTROState { config    = cfg }  TCTState
  where m | showVersion cfg             = do vs <- fromConfig version
                                             putPretty $ text $ "The Tyrolean Complexity Tool, Version " ++ vs
          | showHelp cfg                = putPretty $ text $ unlines (makeHelpMessage options)
          | isJust $ listStrategies cfg = do Just mreg <- fromConfig listStrategies
                                             let procs = case mreg of 
                                                   Just reg -> [ proc | proc <- toProcessorList (processors cfg)
                                                                      , matches reg (name proc) || matches reg (unlines (description proc))]
                                                   Nothing  -> toProcessorList (processors cfg)
                                                 p1 `ord` p2     = name p1 `compare` name p2 ;
                                                 matches reg str = isJust $ matchRegex (mkRegex reg) str ;
                                             putPretty $ text "" $+$ vcat [pprint proc $$ (text "") | proc <- sortBy ord procs]
          | otherwise                   = do prob <- readProblem
                                             procs <- fromConfig processors
                                             getProc <- fromConfig processor
                                             proc <- liftEIO $ getProc prob procs
                                             proof <- process proc prob
                                             putPretty (pprint $ answer proof)
                                             when (showProof cfg) (putPretty $ text "" $+$ pprint proof)
                 
        readProblem = do file <- fromConfig problemFile 
                         maybeAT <- fromConfig answerType 
                         parsedResult <- liftIO $ ProblemParser.problemFromFile file
                         case parsedResult of
                           Left err                              -> throwError $ ProblemParseError err
                           Right (prob, warns) | wellFormed prob -> mapM_  (warn . ProblemParseWarning) warns >> overwriteAnswerType maybeAT prob
                                               | otherwise       -> throwError $ ProblemNotWellformed prob


        process proc prob  = do gs <- fromConfig getSolver
                                slver <- liftEIO $ gs
                                lf <- fromConfig logFile
                                liftIO $ case lf of
                                              Nothing -> runSolver (SolverState slver) (apply proc prob :: StdSolverM (Proof SomeProcessor))
                                              Just f  -> C.block $ do h <- openFile f WriteMode  -- TODO error handling
                                                                      st <- initialState h (SolverState slver)
                                                                      r <- runSolver st (apply proc prob :: LoggingSolverM StdSolverM (Proof SomeProcessor))
                                                                      hFlush h >> hClose h
                                                                      return r


                         
        overwriteAnswerType Nothing   prob                         = return $ prob 
        overwriteAnswerType (Just at) prob | consistent prob' prob = return prob'
                                           | otherwise             = throwError AnswerTypeMisMatch
            where  prob' = onProblem 
                           (\ _ _ trs         -> standardProblem
                                                 (terms (atype at) (Trs.definedSymbols trs) (Trs.constructors trs))
                                                 (strat (atype at))
                                                 trs)
                           (\ _ _ dp trs      -> dpProblem
                                                 (terms (atype at) (Trs.definedSymbols dp) (Trs.constructors trs))
                                                 (strat (atype at))
                                                 dp
                                                 trs)
                           (\ _ _ strict weak -> let both = strict `Trs.union` weak
                                                 in relativeProblem
                                                    (terms (atype at) (Trs.definedSymbols both) (Trs.constructors both))
                                                    (strat (atype at))
                                                    strict
                                                    weak)
                         prob
                   terms DC  _ _   = Prob.TermAlgebra
                   terms IDC _ _   = Prob.TermAlgebra
                   terms RC ds cs  = Prob.BasicTerms ds cs
                   terms IRC ds cs = Prob.BasicTerms ds cs
                   strat DC  = Prob.Full
                   strat IDC = Prob.Innermost
                   strat RC  = Prob.Full
                   strat IRC = Prob.Innermost
                   consistent p1 p2 = if isStrict at then p1 == p2 else True                   
-- -check :: Problem -> TCT (Proof SomeProcessor)
-- -check prob = do fn <- askConfig process
-- -                getProc <- askConfig getProcessor
-- -                proc <- getProc prob
-- -                fn proc probundefined


parseArguments :: Config -> ErroneousIO Config
parseArguments defaults = 
    do as <- liftIO $ getArgs
       case parseOptions options (\inputFile f -> f {problemFile = inputFile}) defaults as of
         Right f  -> return f
         Left err  -> throwError $ FlagsParseError err
