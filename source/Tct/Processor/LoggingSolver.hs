{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE TypeFamilies #-}

-----------------------------------------------------------------------------------
-- |
-- Module      :  Tct.Processor.LogginSolver
-- Copyright   :  (c) Martin Avanzini <martin.avanzini@uibk.ac.at>, 
--                Georg Moser <georg.moser@uibk.ac.at>, 
--                Andreas Schnabl <andreas.schnabl@uibk.ac.at>
-- License     :  LGPL (see COPYING)
-- Maintainer  :  Martin Avanzini <martin.avanzini@uibk.ac.at>
-- Stability   :  unstable
-- Portability :  unportable      
--
-- This module provides an implementation of 'P.SolverM' that
-- performs logging of processor calls.
----------------------------------------------------------------------------------



module Tct.Processor.LoggingSolver where
import Control.Concurrent.Chan
import Control.Concurrent.MVar
import System.CPUTime (getCPUTime)
import System.IO (Handle, hPutStrLn, hFlush)
import Control.Concurrent (ThreadId, forkIO, myThreadId)
import qualified Control.Exception as C
import Text.PrettyPrint.HughesPJ
import Control.Monad.RWS.Lazy hiding ((<>))
import System.Locale 

import Data.Time.Clock (getCurrentTime, picosecondsToDiffTime, UTCTime(..))
import Data.Time.Format (formatTime)
import Data.Time.LocalTime (utcToLocalZonedTime, ZonedTime(..))
import Termlib.Problem
import Termlib.Utils

import Tct.Main.Debug
import Tct.Processor as P

-- add logging to solver monad
data LoggingMsg = LoggingMsg Message Int (Integer, ZonedTime) ThreadId (InstanceOf SomeProcessor) Problem 

toSec :: Integer -> Double
toSec i = fromInteger i / fromInteger ((10 :: Integer)^(12 :: Integer))

instance PrettyPrintable LoggingMsg where 
    pprint (LoggingMsg sig lv (cpuTime,time) thread inst prob) = 
        stars <+> ( heading 
                   $+$ properties 
                   $+$ text "" 
                   $+$ body 
                   $+$ text "")
        where heading = text (case sig of {SolveStart -> "START"; _ -> "FINISH"})
                        <+> text "*" <> text (P.instanceName inst) <> text "*"
                        <+> text "@"
                        <+> text (show cpuTime_ms ++ "ms")
                        <+> (case sig of {SolveFinish p -> pprint (answer p) ; _ -> text "" })

              cpuTime_ms :: Int
              cpuTime_ms = round $ (fromInteger cpuTime  :: Double) / (10.0^(9 :: Int))
              stars = text [ '*' | _ <- [1..indent]] 
              indent = lv * 2 - 1 -- case sig of {SolveStart -> lv; _-> lv + 1}

              timedoc = text ("<" ++ timestring ++ "." ++ picos ++ ">")
                  where picos = take 6 $ formatTime defaultTimeLocale "%q" time
                        timestring = formatTime defaultTimeLocale "%F %H:%M:%S" time

              body = text "#+BEGIN_EXAMPLE"
                     $+$ (case sig of 
                            SolveStart -> pprint prob
                            SolveFinish p -> pprintProof p StrategyOutput)
                     $+$ text "#+END_EXAMPLE"

              ppPropertyName n = text $ ":" ++ n ++ ":"

              properties = text ":PROPERTIES:"
                           $+$ vcat [ ppPropertyName n <+> a | (n,a) <- props]
                           $+$ ppPropertyName "COLUMNS" <+> hsep [text "%" <> text n | (n,_) <- props]
                           $+$ text ":END:"
                  where props = case sig of
                                  SolveStart    -> globalProps ++ [("Answer", empty)]
                                  SolveFinish r -> globalProps ++ [("Answer", pprint $ answer r)]
                        globalProps =  [ ("Status", case sig of 
                                                      SolveStart -> text $ "START"
                                                      _       -> text $ "END")
                                       , ("Processor", text $ instanceName inst)
                                       , ("Thread", text $ show thread)
                                       , ("Strategy", text $ show $ strategy prob)
                                       , ("Start-Terms", case startTerms prob of 
                                                           TermAlgebra {} -> text $ "Terms"
                                                           BasicTerms {}  -> text $ "Basic")
                                       , ("Clock", timedoc)]



newtype LoggingSolverM m r = LS (RWST (Chan (Maybe LoggingMsg), UTCTime) [()] Int m r)
    deriving (Monad, MonadIO, MonadReader (Chan (Maybe LoggingMsg), UTCTime), MonadState Int, MonadTrans)


data LSolverState st = LSolverState { subState  :: st
                                    , level :: Int
                                    , startTime :: UTCTime
                                    , logHandle :: Handle }


initialState :: Handle -> st -> IO (LSolverState st)
initialState h substate =  
  do t' <- getCurrentTime
     return $ LSolverState { subState = substate
                           , level = 1
                           , startTime = t' 
                           , logHandle = h }


runLS :: Monad m => LoggingSolverM m r -> Chan (Maybe LoggingMsg) -> UTCTime -> Int -> m r
runLS (LS m) chan time lv = do (a,_,_) <- runRWST m (chan,time) lv 
                               return a

instance SolverM m => SolverM (LoggingSolverM m) where 
    type St (LoggingSolverM m) = LSolverState (St m)

    mkIO m = do (chan,time) <- ask
                lv   <- get
                m' <- lift $ mkIO $ runLS m chan time lv
                return $ m'

    satSolver = lift satSolver
    runSolver st m = do chan <- liftIO $ newChan
                        mv <- liftIO $ newEmptyMVar
                        let handle = logHandle st
                            time   = startTime st
                        mapM_ (hPutStrLn handle) [ "-*- mode: Org; mode: Auto-Revert -*-"
                                                 , "#+STARTUP: hidestars"
                                                 , "#+STARTUP: hideall"
                                                 , "#+STARTUP: odd"
                                                 , "#+TODO: START | END"]
                        let logThread = do mmsg <- readChan chan
                                           case mmsg of 
                                             Just msg -> do hPutStrLn handle (show $ pprint msg)
                                                            hFlush handle
                                                            logThread
                                             Nothing -> putMVar mv ()
                            run = const $ runSolver (subState st) $ runLS m chan time (level st)
                        C.bracket (forkIO logThread) (const $ writeChan chan Nothing >> readMVar mv) run
                        
    solve proc prob = 
      do lv <- get 
         put $ lv + 1
         sendMsg lv SolveStart
         r <- solve_ proc prob 
         sendMsg lv $ SolveFinish $ someProofNode proc prob r 
         return r
        where sendMsg lv sig = 
                do (chan, UTCTime day time) <- ask
                   liftIO $ do pid <- myThreadId
                               cpuTime <- getCPUTime
                               localtime <- utcToLocalZonedTime (UTCTime day (time + picosecondsToDiffTime cpuTime))
                               let inst = (someInstance proc)
                                   msg = LoggingMsg sig lv (cpuTime, localtime) pid inst prob
                               writeChan chan $ Just $ msg
    solvePartial = solvePartial_
