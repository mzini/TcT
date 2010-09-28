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

{-# LANGUAGE GeneralizedNewtypeDeriving, FlexibleInstances #-}

module Tct.Main 
    ( tct
    , Config (..)
    , defaultConfig
    )
where


import Control.Concurrent (killThread, forkOS)
import Control.Concurrent.MVar (putMVar, readMVar, newEmptyMVar)
import Control.Monad.Trans (liftIO)
import Data.Maybe (isJust, fromMaybe)
import Data.List (sortBy)
import System
import System.Posix.Signals (Handler(..), installHandler, sigTERM)
import Text.PrettyPrint.HughesPJ
import Text.Regex (mkRegex, matchRegex)
import qualified Config.Dyre as Dyre
import qualified Control.Exception as C

import Termlib.Utils (PrettyPrintable (..))

import Tct (Config (..), defaultConfig, run)
import Tct.Main.Flags (getFlags, Flags(..), helpMessage)
import Tct.Processor (Processor (..), ParsableProcessor (..), processors, name)
import qualified Tct.Main.Version as V

showError :: Config -> String -> Config
showError cfg msg = cfg { errorMsg = msg : errorMsg cfg }

runTct :: Config -> Flags -> IO ExitCode
runTct cfg flgs | showVersion flgs                  = do putStrLn $ "The Tyrolean Complexity Tool, Version " ++ version cfg
                                                         return ExitSuccess
                | showHelp flgs                     = do putStrLn $ unlines helpMessage
                                                         return ExitSuccess
                | listStrategies flgs /= Nothing    = do let matches reg str = isJust $ matchRegex (mkRegex reg) str
                                                             p1 `ord` p2 = name p1 `compare` name p2
                                                             procs = case fromMaybe (error "cannot happen") (listStrategies flgs) of 
                                                                       Just reg -> [ proc | proc <- processors (parsableProcessor cfg)
                                                                                          , matches reg (name proc) 
                                                                                                        || matches reg (unlines (description proc))]
                                                                       Nothing  -> processors (parsableProcessor cfg)
                                                         putStrLn $ show $ text "" $+$ vcat [pprint proc $$ (text "") | proc <- sortBy ord procs]
                                                         return ExitSuccess
                | otherwise        = do (r,warns) <- liftIO $ run flgs cfg
                                        putWarnMsg [show $ pprint warn | warn <- warns]
                                        case r of 
                                          Just e  -> putErrorMsg [(show $ pprint e)] >> return exitFail
                                          Nothing -> return ExitSuccess


putErrorMsg :: [String] -> IO ()
putErrorMsg str = do putStrLn "MAYBE"
                     putStrLn ""
                     putStrLn $ unlines $ "The following error(s) occured:" : "" : str

putWarnMsg :: [String] -> IO ()
putWarnMsg []  = return ()
putWarnMsg str = do putStrLn $ unlines $ "The following warning(s) occured:" : "" : str


exitFail :: ExitCode
exitFail = ExitFailure $ -1 


tct :: Config -> IO ()
tct conf = flip Dyre.wrapMain conf params
    where params = Dyre.defaultParams 
                   { Dyre.projectName = "tct"
                   , Dyre.realMain    = realMain
                   , Dyre.showError   = showError
                   , Dyre.configDir   = Just $ configDir conf
                   , Dyre.cacheDir    = Just $ configDir conf
                   , Dyre.statusOut   = const $ return ()
                   , Dyre.ghcOpts     = ["-threaded", "-package tct-" ++ V.version]
                   } 
          realMain cfg | errorMsg cfg /= [] = putErrorMsg (errorMsg cfg) >> exitWith exitFail
                       | otherwise          = do flgs <- readFlags
                                                 mv   <- newEmptyMVar
                                                 _    <- installHandler sigTERM (Catch $ putMVar mv $ exitFail) Nothing
                                                 let main pid = do e <- readMVar mv
                                                                   killThread pid
                                                                   return e
                                                     child = (runTct cfg flgs >>= putMVar mv) 
                                                             `C.catch` \ e -> do putErrorMsg $ ["TCT caught: " ++  show (e :: C.SomeException)]
                                                                                 putMVar mv exitFail
                                                     handler pid (e :: C.SomeException) = do {killThread pid;
                                                                                             putErrorMsg $ [show e];
                                                                                             exitWith exitFail}
                                                 pid <- C.unblock $ forkOS $ child
                                                 e <- main pid `C.catch` handler pid
                                                 exitWith e

          
          readFlags = do fl <- getFlags
                         case fl of  
                           Left err   -> putErrorMsg err >> exitWith exitFail
                           Right flgs -> return flgs
                                                    
                                                              
