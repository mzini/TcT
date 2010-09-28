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

module Tct.Main.Debug where

import Control.Monad.Trans (MonadIO, liftIO)
import Control.Monad (liftM)
import Control.Monad.Error (MonadError, catchError, throwError)
import System.CPUTime (getCPUTime)
import System.IO
import System.IO.Unsafe

import Termlib.Utils (PrettyPrintable (..))

debugEnabled :: Bool
debugEnabled = False

putErrLn :: String -> IO ()
putErrLn s = hPutStr stderr (s ++ "\n")

whenDebug :: a -> a -> a
whenDebug a b = if debugEnabled then a else b

printTime :: Integer -> String
printTime t = show $ (fromIntegral t / (10^(9::Integer)) :: Double)

printTimeLn :: MonadIO m => Maybe Integer -> String -> m Integer
printTimeLn mt s = liftIO $ do {t <- getCPUTime; putErrLn $ "[" ++ ts t ++ "] " ++ s ++ " " ++ e; return t}
    where e = maybe "start" (const "end") mt
          ts t2 = maybe (printTime t2) (\ t1 -> printTime t1 ++ "+" ++ printTime (t2 - t1)) mt


timedLog :: MonadIO m => String -> m a -> m a
timedLog s m = whenDebug dm m
        where dm = do t1 <- printTimeLn Nothing s
                      a <- seq t1 m
                      _ <- seq a $ printTimeLn (Just t1) s
                      return a


timedLogCatchErr :: (MonadIO m, MonadError e m) => String -> m a -> m a
timedLogCatchErr s m = whenDebug dm m
        where dm = do t1 <- printTimeLn Nothing s
                      a <- seq t1 ((Right `liftM` m) `catchError` (return . Left))
                      _ <- seq a $ printTimeLn (Just t1) s
                      case a of 
                        Right a' -> return a'
                        Left e -> throwError e

debugMsg :: MonadIO m => String -> m ()
debugMsg = whenDebug (liftIO . putErrLn) (const $ return ())


unsafeDebugMsg :: Show a => a -> a
unsafeDebugMsg a = unsafePerformIO (debugMsg (show a) >> return a)

unsafeDebugMsgPP :: PrettyPrintable a => a -> a
unsafeDebugMsgPP a = unsafePerformIO (debugMsg (show $ pprint $ a) >> return a)