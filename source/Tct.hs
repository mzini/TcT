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
import Termlib.Utils (PrettyPrintable (..), paragraph)
import qualified Termlib.Problem as Prob
import qualified Termlib.Problem.ParseErrors as ProblemPEs
import qualified Termlib.Problem.Parser as ProblemParser
import qualified Termlib.Trs as Trs

import Tct.Main.Flags 
import Tct.Processor
import Tct.Processor.LoggingSolver
import Tct.Proof
import qualified Tct.Main.Version as Version
import Tct.Processor.Timeout (timeout)
import qualified Tct.Methods as Methods

data Config = Config { processors        :: AnyProcessor
                     , process           :: InstanceOf SomeProcessor -> Problem -> TCT (Proof SomeProcessor)
                     , defaultProcessor  :: Problem -> TCT (InstanceOf SomeProcessor)
                     , getProcessor      :: Problem -> TCT (InstanceOf SomeProcessor)
                     , getProblem        :: TCT Problem
                     , getSolver         :: TCT SatSolver
                     , showProof         :: (Proof SomeProcessor) -> TCT String
                     , satSolver         :: SatSolver
                     , configDir         :: IO FilePath
                     , errorMsg          :: [String]
                     , version           :: String}


data TCTError = StrategyParseError String
              | ProblemParseError ProblemPEs.ParseError
              | ProblemUnknownFileError String
              | ProblemNotWellformed Problem
              | AnswerTypeMisMatch
              | ProblemMissingError 
              | SatSolverMissing String
              | SomeExceptionRaised C.SomeException
              | UnknownError String deriving (Typeable)

instance Show Tct.TCTError where show = show . pprint


data TCTWarning = ProblemParseWarning ProblemPEs.ParseWarning deriving Show

data TCTState = TCTState

data TCTROState = TCTROState 
  { config    :: Config
  , flags     :: Flags}


instance Error TCTError where
  strMsg = UnknownError


newtype TCT r = TCT { 
    tct :: ErrorT TCTError (RWST TCTROState [TCTWarning] TCTState IO) r
  } deriving (Monad, MonadIO, MonadError TCTError, MonadReader TCTROState)

getStrategyString :: TCT (Maybe String)
getStrategyString = do mstr <- askFlag strategy
                       mfn <- askFlag strategyFile
                       case (mstr, mfn) of 
                         (Just _, _)        -> return $ mstr
                         (Nothing, Just fn) -> liftIO $ (Just `liftM` readFile fn) `catch` (const $ return Nothing)
                         _                  -> return Nothing


-- TODO are those fields in the config really interesting, what are interesting fields?
defaultConfig :: Config
defaultConfig = Config { processors       = processors_ 
                       , process          = process_
                       , defaultProcessor = defaultProcessor_
                       , getProcessor     = getProcessor_
                       , getProblem       = getProblem_
                       , getSolver        = getSolver_
                       , showProof        = showProof_ 
                       , satSolver        = MiniSat "minisat" -- TODO pfad und exe unterscheiden
                       , configDir        = do home <- getHomeDirectory 
                                               return $ home </> ".tct"
                       , errorMsg         = []
                       , version          = Version.version
                       }

    where processors_         = Methods.defaultProcessor

          process_ proc prob  = do gs <- askConfig getSolver
                                   slver <- gs
                                   lf <- askFlag logFile
                                   liftIO $ case lf of
                                              Nothing -> runSolver (SolverState slver) (apply proc prob :: StdSolverM (Proof SomeProcessor))
                                              Just f  -> C.block $ do h <- openFile f WriteMode  -- TODO error handling
                                                                      st <- initialState h (SolverState slver)
                                                                      r <- runSolver st (apply proc prob :: LoggingSolverM StdSolverM (Proof SomeProcessor))
                                                                      hFlush h >> hClose h
                                                                      return r 

          getProblem_        = do inputFile <- input `liftM` askFlags
                                  parseResult <- liftIO $ ProblemParser.problemFromFile inputFile
                                  case parseResult of 
                                    Left err            -> throwError $ ProblemParseError err
                                    Right (prob, warns) -> if wellFormed prob 
                                                           then mapM  (warn . ProblemParseWarning) warns >> overwriteAnswerType prob
                                                           else throwError $ ProblemNotWellformed prob

              where overwriteAnswerType prob =
                        do maybeAT <- answerType `liftM` askFlags
                           case maybeAT of
                             Nothing  -> return prob
                             Just at  -> if consistent prob' at prob 
                                          then return prob'
                                          else throwError AnswerTypeMisMatch
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
                    consistent ans at prob = if isStrict at then ans == prob else True


          defaultProcessor_  = error "defaultProcessor not specified yet!"
          getProcessor_ prob = do anyproc <- askConfig processors
                                  to <- askFlag time
                                  str <- getStrategyString
                                  proc <- case str of 
                                            Just s -> case fromString anyproc s of 
                                                        Left err    -> throwError $ StrategyParseError $ show err
                                                        Right proc' -> return $ someInstance proc'
                                            Nothing -> do defproc <- askConfig defaultProcessor 
                                                          defproc prob
                                  return $ case to of 
                                             Just s ->  someInstance (timeout s proc)
                                             Nothing -> proc

          getSolver_          =  do slver <- getSlver
                                    fn <- findms slver
                                    _ <- checkExe fn
                                    return fn
              where getSlver = do ms <- solver `liftM` askFlags
                                  c  <- askConfigs
                                  case ms of 
                                    Nothing -> return $ satSolver c
                                    Just s  -> return $ MiniSat s
                    findms (MiniSat fn) = do mr <- liftIO $ findExecutable fn
                                             case mr of 
                                               Just s  -> return $ MiniSat s
                                               Nothing -> throwError $ SatSolverMissing "Cannot find sat-solver executable"
                    checkExe slver = do ex <- liftIO $ doesFileExist fp
                                        if ex 
                                         then do p <- liftIO $ getPermissions fp
                                                 if executable p then return fp else throwError $ notexecutable
                                         else throwError $ notexist
                        where fp = exe slver
                              exe (MiniSat n) = n
                              notexist = SatSolverMissing $ "Given executable " ++ fp ++ " does not exist"
                              notexecutable = SatSolverMissing $  "Given filename " ++ fp ++ " is not executable"
          showProof_ proof   = do printproofp <- askFlag proofOutput
                                  return $ show $ pprint (answer proof) $+$  if printproofp 
                                                                              then text "" $+$ pprint proof
                                                                              else empty
                                     

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

readProblem :: TCT Problem
readProblem = do r <- askConfig getProblem
                 r

putProof :: Proof SomeProcessor -> TCT ()
putProof proof = do r <- askConfig showProof 
                    s <- r proof >>= liftIO . evaluate
                    liftIO $ putStrLn s

liftS :: RWST TCTROState [TCTWarning] TCTState IO r -> TCT r
liftS m = TCT $ lift m

warn :: TCTWarning -> TCT ()
warn w = liftS $ tell [w]

askFlags :: TCT Flags
askFlags = ask >>= return . flags

askFlag :: (Flags -> a) -> TCT a
askFlag f = f `liftM` askFlags


askConfigs :: TCT Config
askConfigs = ask >>= return . config

askConfig :: (Config -> a) -> TCT a
askConfig f = do c <- askConfigs
                 return $ f c

pprintErr :: String -> Doc -> Doc
pprintErr m e = nest 1 $ paragraph m <> text ":" $$ (nest 2 $ e)

instance PrettyPrintable TCTError where 
  pprint (StrategyParseError s) = pprintErr "Error when parsing strategy" $ text $ s
  pprint (ProblemParseError e) = pprintErr "Error when parsing problem" $ pprint e
  pprint ProblemMissingError = text "No problem supplied"
  pprint (UnknownError s) = pprintErr "Unknown error" $ text s
  pprint AnswerTypeMisMatch = text "Answer type does not match problem type"
  pprint (ProblemUnknownFileError s) = pprintErr "Don't know how to parse file" $ quotes (text s) 
  pprint (ProblemNotWellformed prob) = pprintErr "The problem does not contain well-formed TRSs" $ pprint prob
  pprint (SatSolverMissing e)        = pprintErr "There is a problem with the MiniSat executable. Please specify appropriately with flag -minisat. Reason was" $ text e
  pprint (SomeExceptionRaised e)     = pprintErr "The following exception was raised during computation" (text $ show e)



instance PrettyPrintable TCTWarning where
  pprint (ProblemParseWarning w) = pprintErr "Warning when parsing problem" $ pprint w

instance PrettyPrintable [TCTWarning] where
  pprint [] = empty
  pprint ws = fsep [pprint w | w <- ws]
