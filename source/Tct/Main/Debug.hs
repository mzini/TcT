{-# OPTIONS_HADDOCK hide #-}
--------------------------------------------------------------------------------
-- | 
-- Module      :  Tct.Main.Debug
-- Copyright   :  (c) Martin Avanzini <martin.avanzini@uibk.ac.at>, 
--                Georg Moser <georg.moser@uibk.ac.at>, 
--                Andreas Schnabl <andreas.schnabl@uibk.ac.at>,
-- License     :  LGPL (see COPYING)
--
-- Maintainer  :  Martin Avanzini <martin.avanzini@uibk.ac.at>
-- Stability   :  unstable
-- Portability :  unportable      
-- 
-- Debug Utilities.
--------------------------------------------------------------------------------   

module Tct.Main.Debug where
-- MA:TODO: output to stream specified in Tct.Config, integrate in solver monad

import System.IO
import Tct.Processor(Proof, SomeProcessor)

import Termlib.Utils (PrettyPrintable (..))

data Message = SolveStart 
             | SolveFinish (Proof SomeProcessor)

class DebugM m where
  setDebug     :: Bool -> m ()
  debugEnabled :: m Bool
  debugMsgPut  :: PrettyPrintable body => Int -> String -> Maybe body -> m ()
  
putErrLn :: String -> IO ()
putErrLn s = hPutStr stderr (s ++ "\n")

