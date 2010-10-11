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
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE TypeFamilies #-}

module Tct.Processor.LoggingSolver where
import Control.Concurrent.Chan
import Control.Concurrent.MVar
import System.CPUTime (getCPUTime)
import System.IO (Handle, hPutStrLn, hFlush)
import Control.Concurrent (ThreadId, forkIO, myThreadId)
import qualified Control.Exception as C
import Text.PrettyPrint.HughesPJ
import Control.Monad.RWS.Lazy
import Data.UUID
import System.UUID.V4

import Data.Time.Clock (getCurrentTime, picosecondsToDiffTime, UTCTime(..))
import Data.Time.Format (formatTime)
import Data.Time.LocalTime (utcToLocalZonedTime, ZonedTime(..))
import Termlib.Problem
import Termlib.Utils
import Locale

import Tct.Processor as P
import Tct.Proof

-- add logging to solver monad
data LoggingSig = LMStart 
                | LMFin (Proof SomeProcessor)
data LoggingMsg = LoggingMsg UUID LoggingSig Int (Integer, ZonedTime) ThreadId (InstanceOf SomeProcessor) Problem 

toSec :: Integer -> Double
toSec i = fromInteger i / fromInteger ((10 :: Integer)^(12 :: Integer))

instance PrettyPrintable LoggingMsg where 
    pprint (LoggingMsg uid sig lv (cpuTime,time) thread inst prob) = 
        stars <+> ( heading 
                   $+$ properties 
                   $+$ text "" 
                   $+$ body 
                   $+$ text "")
        where heading = text (case sig of {LMStart -> "START"; _ -> "END"})
                        <+> text "*" <> text (P.instanceName inst) <> text "*"
                        <+> brackets ppId
                        <+> text "@"
                        <+> text (show cpuTime_ms ++ "ms")

              cpuTime_ms :: Int
              cpuTime_ms = round $ (fromInteger cpuTime  :: Double) / (12.0^(9 :: Int))
              stars = text [ '*' | _ <- [1..indent]] 
              indent = lv -- case sig of {LMStart -> lv; _-> lv + 1}

              ppId = text $ take 8 $ show $ uid

              timedoc = text ("<" ++ timestring ++ "." ++ picos ++ ">")
                  where picos = take 6 $ formatTime defaultTimeLocale "%q" time
                        timestring = formatTime defaultTimeLocale "%F %H:%M:%S" time

              body = text "#+BEGIN_EXAMPLE"
                     $+$ (case sig of 
                            LMStart -> prettyPrintRelation prob
                            LMFin p -> pprint p)
                     $+$ text "#+END_EXAMPLE"

              ppPropertyName n = text $ ":" ++ n ++ ":"

              properties = text ":PROPERTIES:"
                           $+$ vcat [ ppPropertyName n <+> a | (n,a) <- props]
                           $+$ ppPropertyName "COLUMNS" <+> hsep [text "%" <> text n | (n,_) <- props]
                           $+$ text ":END:"
                  where props = case sig of
                                  LMStart -> globalProps ++ [("Answer", empty)]
                                  (LMFin r) -> globalProps ++ [("Answer", pprint $ answer r)]
                        globalProps =  [ ("Status", case sig of 
                                                      LMStart -> text $ "START"
                                                      _       -> text $ "END")
                                       , ("Processor", text $ instanceName inst)
                                       , ("Thread", text $ show thread)
                                       , ("Strategy", text $ show $ strategy prob)
                                       , ("Start-Terms", case startTerms prob of 
                                                           TermAlgebra -> text $ "Terms"
                                                           _           -> text $ "Basic")
                                       , ("Id", ppId)
                                       , ("Clock", timedoc)]



newtype LoggingSolverM m r = LS (RWST (Chan (Maybe LoggingMsg), UTCTime) [()] Int m r)
    deriving (Monad, MonadIO, MonadReader (Chan (Maybe LoggingMsg), UTCTime), MonadState Int, MonadTrans)


data LSolverState st = LSolverState { subState  :: st
                                    , level :: Int
                                    , startTime :: UTCTime
                                    , logHandle :: Handle }


initialState :: Handle -> st -> IO (LSolverState st)
initialState h substate =  do t' <- getCurrentTime
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
                return $ C.block $ m'

    runSolver st m = do chan <- liftIO $ newChan
                        mv <- liftIO $ newEmptyMVar
                        let handle = logHandle st
                            time   = startTime st
                        mapM_ (hPutStrLn handle) [ "-*- mode: Org; mode: Auto-Revert -*-"
                                                 , "#+STARTUP: hidestars"
                                                 , "#+STARTUP: hideall"
                                                 , "#+TODO: START | END"]
                        let logThread = do mmsg <- readChan chan
                                           case mmsg of 
                                             Just msg -> do hPutStrLn handle (show $ pprint msg)
                                                            hFlush handle
                                                            logThread
                                             Nothing -> putMVar mv ()
                            run = const $ C.block $ runSolver (subState st) $ runLS m chan time (level st)
                        C.bracket (forkIO logThread) (const $ writeChan chan Nothing >> readMVar mv) run
                        

    minisatValue m e = lift $ minisatValue m e 
                       
    solve proc prob = do lv <- get 
                         uid <- liftIO $ uuid
                         put $ lv + 1
                         sendMsg uid lv LMStart
                         r <- solve_ proc prob 
                         sendMsg uid lv $ LMFin $ Proof { appliedProcessor = someInstance proc 
                                                        , inputProblem = prob
                                                        , result = someProof r}
                         return r
        where sendMsg uid lv sig = do (chan, UTCTime day time) <- ask
                                      liftIO $ do pid <- myThreadId
                                                  cpuTime <- getCPUTime
                                                  localtime <- utcToLocalZonedTime (UTCTime day (time + picosecondsToDiffTime cpuTime))
                                                  let inst = (someInstance proc)
                                                      msg = LoggingMsg uid sig lv (cpuTime, localtime) pid inst prob
                                                  writeChan chan $ Just $ msg
