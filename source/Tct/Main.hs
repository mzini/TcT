{- |
Module      :  Tct.Main
Copyright   :  (c) Martin Avanzini <martin.avanzini@uibk.ac.at>, 
               Georg Moser <georg.moser@uibk.ac.at>, 
               Andreas Schnabl <andreas.schnabl@uibk.ac.at>,
License     :  LGPL (see COPYING)

Maintainer  :  Martin Avanzini <martin.avanzini@uibk.ac.at>
Stability   :  unstable
Portability :  unportable      


This module provides the main function of TcT.
-}


module Main (
  main
  ) where

import Tct

-- | This is the main function of the executable 'tct'.
main :: IO ()
main = tct defaultConfig


