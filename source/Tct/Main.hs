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
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE GeneralizedNewtypeDeriving, FlexibleInstances #-}

module Tct.Main 
    ( tct
    , defaultConfig
    , Config (..)
    )
where


import Control.Concurrent (killThread, forkOS)
import Control.Concurrent.MVar (putMVar, readMVar, newEmptyMVar)
import Control.Monad.Error (runErrorT, Error (..))
import Control.Monad.Trans (liftIO)
import System
import System.Posix.Signals (Handler(..), installHandler, sigTERM, sigPIPE)
import qualified Config.Dyre as Dyre
import qualified Control.Exception as C

import Tct (Config (..), defaultConfig, runTct, TCTError (..), parseArguments, runErroneous)
import qualified Tct.Main.Version as V

instance C.Exception Tct.TCTError


exitFail :: ExitCode
exitFail = ExitFailure $ -1 

tct :: Config -> IO ()
tct conf = do ecfg <- runErrorT (configDir conf) 
              case ecfg of 
                Left e -> putErrorMsg e
                Right dir -> flip Dyre.wrapMain conf Dyre.defaultParams { Dyre.projectName = "tct"
                                                                        , Dyre.realMain    = realMain
                                                                        , Dyre.showError   = \ cfg msg -> cfg { errorMsg = msg : errorMsg cfg }
                                                                        , Dyre.configDir   = Just $ return dir
                                                                        , Dyre.cacheDir    = Just $ return dir
                                                                        , Dyre.statusOut   = const $ return ()
                                                                        , Dyre.ghcOpts     = ["-threaded", "-package tct-" ++ V.version] } 
  where putErrorMsg = putError conf
        putWarnings = mapM_ (putWarning conf)
        realMain cfg | errorMsg cfg /= [] = C.block $ mapM (putErrorMsg . strMsg) (errorMsg conf) >> exitWith exitFail
                     | otherwise          = C.block $ do mv   <- newEmptyMVar
                                                         _    <- installHandler sigTERM (Catch $ putMVar mv $ exitFail) Nothing
                                                         _    <- installHandler sigPIPE (Catch $ putMVar mv $ ExitSuccess) Nothing
                                                         let main pid = do {e <- readMVar mv; killThread pid; return e}
                                                             child = (C.unblock tctProcess >>= putMVar mv) 
                                                                     `C.catch` \ (e :: C.SomeException) -> putErrorMsg (SomeExceptionRaised e) >> putMVar mv exitFail
                                                             handler pid (e :: C.SomeException) = do killThread pid
                                                                                                     putErrorMsg $ (SomeExceptionRaised e)
                                                                                                     exitWith exitFail
                                                         pid <- forkOS $ child
                                                         e <- main pid `C.catch` handler pid
                                                         exitWith e
        tctProcess = do r <- runErroneous $ do warns <- parseArguments conf >>= runTct
                                               liftIO $ putWarnings warns
                                               return ExitSuccess
                        case r of 
                          Left err  -> putErrorMsg err >> return exitFail
                          _         -> return ExitSuccess

                                                              
