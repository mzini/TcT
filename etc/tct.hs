#!/usr/bin/runhaskell

import Prelude hiding (fail, uncurry)
import Tct.Configuration
import Tct.Interactive
import Tct.Instances
import qualified Tct.Processors as Processor
import qualified Termlib.Repl as TR

main :: IO ()
main = tct config

config :: Config
config = defaultConfig { strategies = strats
                       , interactiveShowProofs = True
                       , recompile = False } 
  where
    strats = [ matrices ::: strategy "matrices" ( optional naturalArg "start" (Nat 1)
                                                  :+: naturalArg )
             , withDP   ::: strategy "withDP" ]
      
    
matrices (Nat start :+: Nat n) = 
  fastest [ matrix `withDimension` d `withBits` bitsFor d | d <- [start..start+n] ] 
  where
    bitsFor d | d < 3     = 2 
              | otherwise = 1

withDP = 
  (timeout 5 dps <> dts)
  >>> try (exhaustively partitionIndependent)
  >>> try cleanTail
  >>> try usableRules 
  where 
    dps = dependencyPairs >>> try usableRules >>> wgOnUsable
    dts = dependencyTuples
    wgOnUsable = weightgap `withDimension` 1 `wgOn` WgOnTrs
      