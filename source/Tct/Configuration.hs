--------------------------------------------------------------------------------
-- | 
-- Module      :  Tct.Configuration
-- Copyright   :  (c) Martin Avanzini <martin.avanzini@uibk.ac.at>, 
--                Georg Moser <georg.moser@uibk.ac.at>, 
--                Andreas Schnabl <andreas.schnabl@uibk.ac.at>,
-- License     :  LGPL (see COPYING)
--
-- Maintainer  :  Martin Avanzini <martin.avanzini@uibk.ac.at>
-- Stability   :  unstable
-- Portability :  unportable      
-- 
-- In this section we describe the configuration of 'TcT', both 
-- influencing the command line interface (cf. "Tct.CommandLine")
-- and the interactive interface (cf. "Tct.Interactive").
--
-- The command line interface supports various flags that govern the
-- behaviour of TcT, cf. "Tct.CommandLine".
-- A more expressive way to configure TcT is to alter the
-- configuration file 'tct.hs', usually residing in the directory '${HOME}\/.tct'. 
-- In fact, this configuration file is a Haskell script (cf. <http://haskell.org>), 
-- which implies that this extended way of configuring TcT requires a 
-- Haskell compiler to be installed on your system. The main advantage of 
-- this approach is that the full expressiveness of Haskell can be used, 
-- in particular when defining custom processors. 
-- 
-- >>> cat ${HOME}/.tct/tct.hs
-- #!/usr/bin/runhaskell
-- .
-- import Prelude hiding (fail, uncurry)
-- import Tct.Configuration
-- import Tct.Interactive
-- import Tct.Instances
-- import qualified Tct.Instances as Instance
-- import qualified Tct.Processors as Processor
-- import qualified Termlib.Repl as TR
-- .
-- .
-- config :: Config
-- config = defaultConfig
-- .
-- main :: IO ()
-- main = tct config
--
-- The above output shows the minimal configuration. 
-- When started the first time from the command line, TcT will automatically generate
-- the above shown default configuration.  
-- The default configuration imports following modules:
-- 
-- [@"Tct.Configuration"@] This module. It defines the 'defaultConfiguration', 
-- and operators to modify it.
-- 
-- [@"Tct.Interactive"@] This module exposes the functionality of the interactive mode.
--
-- [@"Tct.Instances"@] This module defines operations for constructing (instances of) processors, 
-- together with many combinators.
-- 
-- [@"Tct.Processors"@] This module exports all processors implemented in TcT. These are useful,
-- in the interactive mode, cf. the action 'Tct.Interactive.apply'.
--
-- [@Termlib.Repl@] This module gives access to the /term rewriting library/.
--
-- 
-- The body of the configuration contains two definitions.
-- 
-- [@config :: 'Config'@]
-- This definition defines the configuration of TcT, as explained below.
-- 
-- [@main :: 'IO' ()@]
-- This is the main program. 

--------------------------------------------------------------------------------   

module Tct.Configuration ( 
  -- * The Configuration Object
  -- | Upon startup of TcT, it will alter the configuration 'config' in order to reflect the command line parameters.
  -- Note that the field 'processors' allows adding custom defined processors to
  -- TcT. This is explained in a separate section, see "Tct.Configuration#procs" below.
  Config (..)
  -- | The default configuration shipped with TcT.
  , defaultConfig
  , tct
    
  -- * Specifying Custom Processors 
  -- | #procs#
    
    
           
  -- * Argument Description Combinators
  , Arg (..)
  , Unit (..)
  , (:+:)(..)
  , arg 
  -- | constructs an 'Arg' that is used for parsing at the command line.
  , optional 
  -- | Translates an 'Arg' to an optional argument, by supplying a name 
  -- and a default value
    
  -- ** Built-in Argument Descriptions  #argdescr#
  , ArgInstances.AssocArgument (..)      
  , ArgInstances.Assoc 
  , ArgInstances.assocArg 
  , ArgInstances.boolArg
  , ArgInstances.enumArg
  , ArgInstances.maybeArg
  , ArgInstances.naturalArg
  , ArgInstances.processorArg
  , ArgInstances.EnumOf
  , ArgInstances.Processor
  , ArgInstances.Nat (..)
  , ArgInstances.nat
  , ArgInstances.natToInt
  )
where

import qualified Tct.Interactive as Interactive
import Tct (defaultConfig, Config (..), tct)
import qualified Tct.Processor.Args.Instances as ArgInstances
import Tct.Processor.Args ((:+:)(..), Arg(..), Unit(..), arg, optional)