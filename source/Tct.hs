--------------------------------------------------------------------------------
-- | 
-- Module      :  Tct
-- Copyright   :  (c) Martin Avanzini <martin.avanzini@uibk.ac.at>, 
--                Georg Moser <georg.moser@uibk.ac.at>, 
--                Andreas Schnabl <andreas.schnabl@uibk.ac.at>,
-- License     :  LGPL (see COPYING)
--
-- Maintainer  :  Martin Avanzini <martin.avanzini@uibk.ac.at>
-- Stability   :  unstable
-- Portability :  unportable      
-- 
--------------------------------------------------------------------------------   

{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Tct 
    ( Config (..)
    , TCTError (..)
    , TCTWarning (..)
    , defaultConfig
    , runTct
    , runErroneous
    , tct 
    , processors
    , haddockOptions)
where 

import Control.Concurrent (forkIO, killThread)
import Control.Concurrent.MVar (tryPutMVar, readMVar, newEmptyMVar)
import Control.Monad.Error
import Control.Monad.Instances( )
import Control.Monad.RWS.Lazy hiding ((<>))
import Data.List (sortBy)
import Data.Maybe (isJust)
import Data.Typeable 
import System.Directory
import System.FilePath ((</>))
import System.IO
import System.Environment (getArgs)
import System.Exit
import qualified Data.Set as Set
import Text.PrettyPrint.HughesPJ
import Text.Regex (mkRegex, matchRegex)
import System.Process (system)
import System.Posix.Signals (Handler(..), installHandler, sigTERM)
import System.Posix.Files (ownerReadMode, ownerWriteMode, ownerExecuteMode, unionFileModes, setFileMode)
import qualified Config.Dyre as Dyre
import qualified Control.Exception as C

import Termlib.Problem (Problem, wellFormed)
import qualified Termlib.Problem as Prob
import Termlib.Utils (PrettyPrintable (..), paragraph)
import qualified Termlib.Problem.ParseErrors as ProblemPEs
import qualified Termlib.Problem.Parser as ProblemParser
import qualified Termlib.Trs as Trs

import Tct.Main.Flags
import Tct.Processor
import Tct.Utils.Xml (putXmlProof)
import Tct.Processor.LoggingSolver
import qualified Tct.Main.Version as V
import qualified Tct.Main.Version as Version
import qualified Tct.Instances as Instances
import qualified Tct.Processors as Processors
import qualified Tct.Method.Timeout as Timeout
import qualified Tct.Method.Custom as Custom

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

instance C.Exception Tct.TCTError

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

data OutputMode = OnlyAnswer 
                | WithProof PPMode
                | WithXml

-- | Configuration of TcT. 
data Config = Config { 
  
  -- | This field can be extended by custom strategies.
  strategies        :: [Custom.Strategy]
    
  -- | This fields holds the processor available in TcT.
  , allProcessors        :: AnyProcessor
    
  -- | This field can be used to govern how a processor is 
  -- determined for the loaded problem if no processor is 
  -- supplied at the command line. The second parameter 
  -- refers to the list of available processors.     
  , makeProcessor     :: Problem -> AnyProcessor -> ErroneousIO (InstanceOf SomeProcessor)

  -- | This flag determines if the configuration file should 
  -- be dynamically reloaded.
  , recompile         :: Bool    
    
  -- | This field specifies the configuration dir. It defaults 
  -- to '${HOME}\/.tct'.
  , configDir         :: ErroneousIO FilePath
    
  -- | This field specifies the output mode under which proofs are 
  -- displayed. It defaults to proof output.
  , outputMode        :: OutputMode    
    
  -- | This field may be used to specify a log-file, showing extended
  -- output concerning applications of processors.
  , logFile           :: Maybe FilePath
    
  -- | This field can be used to specify an alternative SAT solver.
  -- Per default, TcT searches for executables 'minisat' or 'minisat2'
  -- in '${PATH}'.
  , getSolver         :: ErroneousIO SatSolver
    
  -- | This field can be used to modify the version.    
  , version           :: String    

    
  -- | This field can be overwritten in order to govern how 
  -- a proof is displayed.
  , putProof          :: Proof SomeProcessor -> PPMode -> IO ()
  
  -- | This field can be overwritten in order to govern how 
  -- an error message is displayed.
  , putError          :: TCTError -> IO ()
  
  -- | This field can be overwritten in order to govern how 
  -- a warning is displayed.
  , putWarning        :: TCTWarning -> IO ()
    
  -- | This field can be used to set an optional timeout, 
  -- in seconds.
  , timeoutAfter      :: Maybe Int
    
  -- | This field holds the file name of the input problem.  
  , problemFile       :: FilePath
  
  -- | When this flag is 'True', interactive mode will print
  -- proofs after execution of commands. 
  , interactiveShowProofs :: Bool
    
  -- | Modified by command line option '--list', cf. "Tct.CommandLine".
  , listStrategies    :: Maybe (Maybe String)
  -- | Modified by command line option '--answer', cf. "Tct.CommandLine".
  , answerType        :: Maybe AnswerType
  -- | Modified by command line option '--help', cf. "Tct.CommandLine".     
  , showHelp          :: Bool
  -- | Modified by command line option '--version', cf. "Tct.CommandLine".
  , showVersion       :: Bool
  -- | Modified by command line option '--interactive', cf. "Tct.CommandLine".    
  , interactive       :: Bool 
  -- | This field holds error messages from dynamic recompilation.
  , errorMsg          :: [String]
  }


-- | This is the default configuration of TcT.
defaultConfig :: Config
defaultConfig = Config { makeProcessor   = defaultProcessor
                       , allProcessors      = Processors.builtInProcessors
                       , strategies      = []
                       , problemFile     = ""
                       , getSolver       = getDefaultSolver
                       , outputMode      = WithProof ProofOutput
                       , putProof        = \ p mde -> hPutPretty stdout (pprintProof p mde)
                       , putError        = \ e -> hPutPretty stderr (pprint e)
                       , putWarning      = hPutPretty stderr . pprint 
                       , configDir       = do home <- liftIO $ getHomeDirectory 
                                              return $ home </> ".tct"
                       , errorMsg        = []
                       , version         = Version.version
                       , recompile       = True
                       , timeoutAfter    = Nothing
                       , answerType      = Nothing
                       , listStrategies  = Nothing
                       , logFile         = Nothing
                       , interactiveShowProofs = False
                       , showHelp        = False
                       , showVersion     = False
                       , interactive     = False}

  where defaultProcessor prob _ = return $ case Prob.startTerms prob of 
          Prob.TermAlgebra {} -> someInstance Instances.dc2012
          _                   -> someInstance Instances.rc2012
        getDefaultSolver = findSatSolver MiniSat "minisat" `catchError` (const $ findSatSolver MiniSat "minisat2")


findSatSolver :: (String -> SatSolver) -> String -> ErroneousIO SatSolver
findSatSolver mk nm = do 
  fn <- findExe 
  checkExe fn
  return $ mk fn
  where findExe :: ErroneousIO FilePath 
        findExe = do mr <- liftIO $ findExecutable nm
                     case mr of 
                       Just s  -> return s 
                       Nothing -> err $ "Cannot find sat-solver executable minisat or minisat2 in your path"
        checkExe :: FilePath -> ErroneousIO ()
        checkExe fn = do exists <- liftIO $ doesFileExist fn
                         unless exists (err $ "Minisat executable '" ++ fn ++ "' is not executable")
                         p <- liftIO $ getPermissions fn
                         unless (executable p) (err $ "Given executable '" ++ fn ++ "' does not exist")
        err = throwError .  SatSolverMissing
        
processorFromString :: String -> AnyProcessor -> ErroneousIO (InstanceOf SomeProcessor)
processorFromString str procs = 
  case fromString procs str of 
    Left err    -> throwError $ StrategyParseError $ show err
    Right proc' -> return proc'

processorFromFile :: FilePath -> AnyProcessor -> ErroneousIO (InstanceOf SomeProcessor)
processorFromFile fn procs =  do
  str <- (liftIO $ readFile fn `C.catch` (\ (_ :: C.SomeException) -> return ""))
  case str of 
    ""  -> throwError (strMsg $ "cannot read strategy from file " ++ fn)
    _   -> processorFromString str procs


hPutPretty :: Handle -> Doc -> IO ()
hPutPretty handle = liftIO . hPutStrLn handle . show

----------------------------------------------------------------------
--- Options
  
options :: Options Config
options =
  [ Option
    { long    = "timeout"
    , short    = "t"
    , meaning = (\n f -> f{ timeoutAfter = Just n }) <$> argNum
    , help    = [ "Maximum running time in seconds."] }
  , Option
    { long    = "verbosity"
    , short    = "v"
    , meaning = let readOutputMode ('a':_) = OnlyAnswer
                    readOutputMode ('p':_) = WithProof ProofOutput
                    readOutputMode ('s':_) = WithProof StrategyOutput
                    readOutputMode ('o':_) = WithProof OverviewOutput                    
                    readOutputMode ('x':_) = WithXml                    
                    readOutputMode md      = error $ "unsupported output mode (this is covered by flagparser anyway): " ++ md
                in (\n f -> f{ outputMode = readOutputMode n }) <$> argOption ["answer","proof","strategy", "overview", "xml", "a", "p", "s", "o", "x"]
    , help    = [ "Verbosity of proof mode."
                , " answer:   print only answer from proof"
                , " proof:    print the full proof"
                , " strategy: print the full proof, enriched with strategy information"
                , " overview: print a minimal proof output, neglecting details"                  
                , " xml:      print xml output"
                , " a:        like answer"
                , " p:        like proof"
                , " s:        like strategy"
                , " o:        like overview"
                , " x:        like xml"] }
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
    { long    = "processor"
    , short    = "s"
    , meaning = (\n f -> f{ makeProcessor = const $ processorFromString n }) <$> argString
    , help    = [ "Specifies the strategy. For a list of strategies see '-l'."]
    }
  , Option
    { long    = "processorfile"
    , short    = "S"
    , meaning = (\n f -> f{ makeProcessor = const $ processorFromFile n }) <$> argFile
    , help    = [ "Like '-s', but reads the strategy from the given file."]
    }
  , Option
    { long    = "list"
    , short   = "l"
    , meaning = (\ n f -> f{ listStrategies = Just n}) <$> argOptString
    , help    = [ "Prints a full list of processors."]
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
    , short    = "z"
    , meaning = (\_ f -> f{ showVersion = True }) <$> argNone
    , help    = [ "Displays the version number."]
    }
  , Option
    { long    = "norecompile"
    , short    = "r"
    , meaning = (\_ f -> f{ recompile = False }) <$> argNone
    , help    = [ "No recompilation of the binaries."]
    }
  , Option
    { long    = "interactive"
    , short    = "i"
    , meaning = (\_ f -> f{ interactive = True }) <$> argNone
    , help    = [ "Start TcT in interactive mode."]
    }
  ]

processors :: Config -> AnyProcessor
processors cfg = 
    fromProcessorList [ Custom.strategyToProcessor s | s <- strategies cfg ]
    <++> allProcessors cfg
                            
haddockOptions :: Doc
haddockOptions = vcat [ ppOpt opt | opt <- options]
  where ppOpt opt = 
            itm opt True $+$ itm opt False 
        itm opt b = 
          (text "[" <> line <> nme <+> text (escape syn) <> text "]")
          $+$ paragraph hlp
          $+$ text ""
            where line | b = text "--"
                       | otherwise = text "-"
                  nme | b = text $ long opt
                      | otherwise = text $ short opt
                  syn = unwords $ args (meaning opt)
                  hlp | b = unlines (help opt)
                      | otherwise = "Same as '-" ++ long opt ++ "'."
        escape = concatMap esc
          where esc c | c `elem` "/'`\"@<[]" = ['\\',c]
                      | otherwise            = [c]
          
        
----------------------------------------------------------------------
-- TCT monad

data TCTState = TCTState
data TCTROState = TCTROState { config    :: Config }

newtype TCT r = TCT (RWST TCTROState [TCTWarning] TCTState ErroneousIO r)
    deriving (Monad, Functor, MonadIO, MonadError TCTError, MonadReader TCTROState, MonadWriter [TCTWarning])

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

runInteractive :: Config -> ErroneousIO ()
runInteractive cfg = 
  do cfgdir <- configDir cfg
     cwd <- liftIO $ 
            (setCurrentDirectory cfgdir >> return True)
            `C.catch` (\ (_:: C.SomeException) -> return False)
     unless cwd (throwError $ strMsg $ 
                 "Changing working directory to " 
                 ++ cfgdir 
                 ++ "failed. We abort.")
     liftIO $ 
       do runGhci `C.catch` (\ (_:: C.SomeException) -> return ())
          putStrLn "Bye, have a nice day!"
          return ()
  where runGhci = system "ghci +RTS -N -RTS" >> return ()
            
runTct :: Config -> ErroneousIO [TCTWarning]
runTct cfg = snd `liftM` evalRWST m TCTROState { config = cfg }  TCTState
  where (TCT m) | showVersion cfg = 
                    do vs <- fromConfig version
                       putPretty $ text $ "The Tyrolean Complexity Tool, Version " ++ vs
                | showHelp cfg = 
                    putPretty $ text $ unlines (makeHelpMessage options)
                | isJust $ listStrategies cfg = 
                    do Just mreg <- fromConfig listStrategies
                       let procs = case mreg of 
                                     Just reg -> [ proc | proc <- toProcessorList (processors cfg)
                                                , matches reg (name proc)]  -- || matches reg (unlines (description proc))
                                     Nothing  -> toProcessorList (processors cfg)
                           p1 `ord` p2     = name p1 `compare` name p2 ;
                           matches reg str = isJust $ matchRegex (mkRegex reg) str ;
                       putPretty $ text "" $+$ vcat [pprint proc $$ (text "") | proc <- sortBy ord procs]
                | otherwise                   = 
                    do (prob,rulelist) <- readProblem
                       procs <- fromConfig processors
                       getProc <- fromConfig makeProcessor
                       proc <- liftEIO $ getProc prob procs
                       tproc <- maybe proc (\ i -> someInstance $ Timeout.timeout i proc) `liftM` fromConfig timeoutAfter
                       proof <- process tproc prob
                       let ans = answer proof
                       liftIO $ C.mask_ $ do 
                         
                         case outputMode cfg of 
                           OnlyAnswer    -> putPretty (pprint ans)
                           WithXml       ->
                             putXmlProof prob rulelist proof ans
                           WithProof mde -> 
                             putPretty $ 
                             pprint ans
                             $+$ text "" 
                             $+$ pprintProof proof mde
                             $+$ text "" 
                             $+$ if succeeded proof 
                                 then text "Hurray, we answered"  <+> pprint ans
                                 else text "Arrrr.."
                 
        readProblem = do file <- fromConfig problemFile 
                         maybeAT <- fromConfig answerType 
                         parsedResult <- liftIO $ ProblemParser.problemFromFile file
                         case parsedResult of
                           Left err -> throwError $ ProblemParseError err
                           Right (prob, rl, warns) 
                                | wellFormed prob -> 
                                    do mapM_  (warn . ProblemParseWarning) warns
                                       prob' <- overwriteAnswerType maybeAT prob
                                       return (prob', rl)
                                | otherwise -> throwError $ ProblemNotWellformed prob


        process proc prob  = do gs <- fromConfig getSolver
                                slver <- liftEIO $ gs
                                lf <- fromConfig logFile
                                liftIO $ case lf of
                                              Nothing -> runSolver (SolverState slver) (apply proc prob :: StdSolverM (Proof SomeProcessor))
                                              Just f  -> do h <- openFile f WriteMode  -- MA:TODO error handling, unblocking
                                                            st <- initialState h (SolverState slver)
                                                            r <- runSolver st (apply proc prob :: LoggingSolverM StdSolverM (Proof SomeProcessor))
                                                            hFlush h >> hClose h
                                                            return r


                         
        overwriteAnswerType Nothing   prob                         = return $ prob 
        overwriteAnswerType (Just at) prob | consistent prob' prob = return prob'
                                           | otherwise             = throwError AnswerTypeMisMatch
            where  prob' = prob { Prob.startTerms = terms (atype at) defineds constructors
                                , Prob.strategy   = strat (atype at)}
                   defineds = Trs.definedSymbols $ Prob.allComponents prob
                   constructors = Trs.constructors $ Prob.allComponents prob
                   terms DC  ds cs = Prob.TermAlgebra $ ds `Set.union` cs
                   terms IDC ds cs = Prob.TermAlgebra $ ds `Set.union` cs
                   terms RC  ds cs = Prob.BasicTerms ds cs
                   terms IRC ds cs = Prob.BasicTerms ds cs
                   strat DC  = Prob.Full
                   strat IDC = Prob.Innermost
                   strat RC  = Prob.Full
                   strat IRC = Prob.Innermost
                   consistent p1 p2 = if isStrict at then p1 == p2 else True                   

parseArguments :: Config -> ErroneousIO Config
parseArguments defaults = 
    do as <- liftIO $ getArgs
       case parseOptions options (\inputFile f -> f {problemFile = inputFile}) defaults as of
         Right f  -> return f
         Left err  -> throwError $ FlagsParseError err

exitFail :: ExitCode
exitFail = ExitFailure $ -1 

data ReturnCode = SigTerm
                -- | SigPipe
                | ExitNormal
                | ExitError TCTError
                deriving Show
                  
-- | This runs TcT with the given configuration. 
-- Use 'defaultConfig' for running TcT with the default configuration.
tct :: Config -> IO ()
tct conf = 
  do r <- runErroneous $ 
        do dir <- getConfigDir
           let dyreConf = 
                 Dyre.defaultParams { Dyre.projectName = "tct"
                                    , Dyre.configCheck = recompile conf
                                    , Dyre.realMain    = \ cfg -> withHandledErrors $ checkSat cfg >> realMain cfg
                                    , Dyre.showError   = \ cfg msg -> cfg { errorMsg = msg : errorMsg cfg }
                                    , Dyre.configDir   = Just $ return dir
                                    , Dyre.cacheDir    = Just $ return dir
                                    , Dyre.statusOut   = hPutStrLn stderr
                                    , Dyre.ghcOpts     = ["-threaded", "-package tct-" ++ V.version] }
             in liftIO $ Dyre.wrapMain dyreConf conf
     case r of 
       Left e -> putErrorMsg e >> exitWith exitFail
       Right () -> exitWith ExitSuccess
  where putErrorMsg = putError conf
        putWarnings = mapM_ (putWarning conf)
        
        getConfigDir = 
          do cfgDir <- configDir conf
             liftIO $ maybeCreateConfigDir cfgDir >> hFlush stdout
             return cfgDir
        
        withHandledErrors eio = do
          r <- runErroneous eio
          case r of 
            Left err -> putErrorMsg err >> exitWith exitFail
            Right ret -> exitWith ret
            
        worker mv conf' = do
          r <- runErroneous $ runTct conf'
          case r of 
            Left err -> do 
              _ <- tryPutMVar mv $ ExitError $ err
              return ()
            Right warns -> do 
              putWarnings warns
              _ <- tryPutMVar mv ExitNormal
              return ()
          
        checkSat conf' = void (getSolver conf')
        
        realMain conf'
          | not (null (errorMsg conf')) = throwError $ UnknownError $ show $ unlines $ errorMsg conf'
          | otherwise = do 
            conf'' <- parseArguments conf'
            if interactive conf''
             then runInteractive conf'' >> return ExitSuccess
             else do
              mv <- liftIO $ newEmptyMVar
              _ <- liftIO $ installHandler sigTERM (Catch $ tryPutMVar mv SigTerm >> return ()) Nothing
              pid <- liftIO $ forkIO $ C.mask $ \ recover -> 
                      recover (worker mv conf'') `C.catch` (\ e -> tryPutMVar mv (ExitError (SomeExceptionRaised e)) >> return ())
              e <- liftIO $ readMVar mv
              liftIO $ killThread pid
              liftIO $ hFlush stdout
              liftIO $ hFlush stderr
              case e of 
                SigTerm -> return exitFail
                -- SigPipe -> exitWith ExitSuccess
                ExitError err -> throwError $ err
                ExitNormal -> return ExitSuccess
              
initialGhciFile :: IO String
initialGhciFile = return $ content
  where content = unlines 
                  [ ":set -package tct"
                  , ":set prompt \"TcT> \""
                  , ":load tct.hs"
                  , ":module +Tct.Interactive"                    
                  , "setConfig config"
                  , "welcome" ]
  
initialConfigFile :: IO String
initialConfigFile = 
  do mrh <- liftIO $ findExecutable "runhaskell"
     return $ maybe content (\ rh -> "#!" ++ rh ++ "\n\n" ++ content) mrh
  
    where content = unlines $ imports ++ ["\n"] ++ funs
          imports = [ "import " ++ maybe m (\ nme -> "qualified " ++ m ++ " as " ++ nme) n
                    | (m,n) <- [ ("Prelude hiding (fail, uncurry)"       , Nothing)
                              , ("Tct (tct)"                            , Nothing)
                              , ("Tct.Configuration"                    , Nothing)                                
                              , ("Tct.Interactive"                      , Nothing)
                              , ("Tct.Instances"                        , Nothing)
                              , ("Tct.Instances"                        , Just "Instance")
                              , ("Tct.Processors"                       , Just "Processor")
                              , ("Termlib.Repl"                         , Just "TR")                                 
                              ]
                    ]
          funs = concat $ 
                 [[ nm ++ " :: " ++ tpe
                  , nm ++ " = " ++ bdy
                  , ""]
                 | (nm,tpe,bdy) <- 
                     [ ("config", "Config", "defaultConfig")
                     , ("main", "IO ()", "tct config") ]]
  
maybeCreateConfigDir :: FilePath -> IO ()
maybeCreateConfigDir cfgdir = 
  do let cfgfile = cfgdir </> "tct.hs"
         ghcifile = cfgdir </> ".ghci"
     maybeCreateDirectory cfgdir
     maybeCreateFile cfgfile True initialConfigFile
     maybeCreateFile ghcifile False initialGhciFile
     
  where maybeCreateDirectory dir = 
          do exists <- catchExceptions False $ doesDirectoryExist dir
             unless exists $ 
               do create ("directory " ++ dir) $ createDirectoryIfMissing True dir
                  setOwnership dir True
                    
        maybeCreateFile file exe mkContent = 
          do exists <- catchExceptions False $ doesFileExist file
             unless exists $ 
               do content <- mkContent
                  let nme | exe       = "executable file " ++ file
                          | otherwise = "file " ++ file
                  create nme $ writeFile file content
                  setOwnership file exe

        setOwnership file exe = catchExceptions () (setFileMode file mde)
          where mde | exe       = rw `unionFileModes` ownerExecuteMode
                    | otherwise = rw
                rw = ownerReadMode `unionFileModes` ownerWriteMode 
        
        create nme m = 
          do putStr $ "Creating " ++ nme ++ " ... "
             success <- catchExceptions False (m >> return True)
             putStrLn $ if success then "Done." else "Fail."

        catchExceptions d m = 
          m `C.catch` (\ (_ :: C.SomeException) -> return d)
