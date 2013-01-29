----------------------------------------------------------------------------------
-- |
-- Module      :  Tct.Utils.Ask
-- Copyright   :  (c) Martin Avanzini <martin.avanzini@uibk.ac.at>, 
--                Georg Moser <georg.moser@uibk.ac.at>, 
--                Andreas Schnabl <andreas.schnabl@uibk.ac.at>
-- License     :  LGPL (see COPYING)
-- Maintainer  :  Martin Avanzini <martin.avanzini@uibk.ac.at>
-- Stability   :  unstable
-- Portability :  unportable      
--
-- This module completing read
----------------------------------------------------------------------------------

module Tct.Utils.Ask 
       (
         ask
       , askStr
       )
       where

import System.Console.Haskeline
import Data.List (isPrefixOf)


completeFromList :: MonadException m => [String] -> String -> m [Completion]
completeFromList lst str = return [simpleCompletion s | s <- lst, str `isPrefixOf` s]

ask :: MonadException m => String -> [String] -> (String -> Maybe a) -> m (Maybe a)
ask prompt options rd = do 
  mr <- runInputT (setComplete completeFN defaultSettings) $ getInputLine prompt
  return $ mr >>= rd
  where
    completeFN = completeWord Nothing " \t" $ completeFromList options

askStr :: MonadException m => String -> [String] -> m (Maybe String)
askStr prompt options = ask prompt options rd 
  where rd str | str `elem` options = Just str
               | otherwise = Nothing