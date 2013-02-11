{-# OPTIONS_HADDOCK prune #-}
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
--------------------------------------------------------------------------------   

module Tct.Configuration ( 
  -- | In this section we describe the configuration of 'TcT', both 
  -- influencing the command line interface (cf. "Tct.CommandLine")
  -- and the interactive interface (cf. "Tct.Interactive").
  --
  -- The command line interface supports various flags that govern the
  -- behaviour of TcT.
  --   Besides basic options given on the command line, TcT can be 
  -- configured by modifying the configuration file.
  -- The configuration file is a Haskell source file that resides in @${HOME}/.tct/tct.hs@ by default, 
  -- and defines the actual binary that is run each time TcT is called. 
  -- Thus the full expressiveness of Haskell is available, 
  -- as a downside, it requires also a working Haskell environment.
  -- 
  -- A minimal configuration is generated automatically on the first run of TcT. 
  -- This initial configuration
  -- constitutes of a set of convenient imports, 
  -- the IO action @main@ together with a /configuration record/ 'Config'.
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
  -- Notably, the body of the default configuration contains two definitions.
  -- 
  -- [@config :: 'Config'@]
  -- This definition defines the configuration of TcT, as explained below. The definition is
  -- mandatory if you want to run the /interactive interface/, cf. "Tct.Interactive".
  -- 
  -- [@main :: 'IO' ()@]
  -- This is the main program. Specifying the main program is mandatory 
  -- for using the /command line interface/ as explained in "Tct.CommandLine".
  -- 
  -- The default configuration imports following modules:
  -- 
  -- [@"Tct.Configuration"@] This module. It defines the 'defaultConfig', 
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
  defaultConfig
  , tct
  -- * The Configuration Record
  -- | The configuration record passed in @main@ allows one 
  -- to predefine various flags of TcT, but most importantly, 
  -- through the field 'strategies' it allows 
  -- the modification of the list of strategies that can be employed. 
  -- Note that option specified at the command line 
  -- overwrite the ones supplied in the config file.
  , Config (..)
      
  -- * Adding Strategies to TcT
  -- | Strategies are added by overwriting the field 'strategies' with a list of 
  -- /strategy declarations/, of the form
  -- 
  -- @
  -- /code/ ::: strategy /name/ [/parameter-declaration/]
  -- @
  --
  -- Here /code/ refers to a value that defines the actual processor, 
  -- /name/ the name of the strategy, and the last component
  -- is used to indicate the arguments of the defined strategy.
  -- 
  -- The following depicts a modified configuration that defines two new 
  -- strategies, called /matrices/ and /withDP/. Observe that one can 
  -- use both transformations and processors, optionally parameterised as  
  -- governed by the @/parameter-declaration/@, as /code/.
  -- 
  -- @  
  -- config :: 'Config'
  -- config = 'defaultConfig' { strategies = strategies } where
  --   strategies = [ matrices ::: strategy \"matrices\" ( 'optional' 'Args.naturalArg' \"start\" 1 :+: 'Args.naturalArg' )
  --                , withDP   ::: strategy \"withDP\" ]
  -- .  
  -- matrices ('Nat' start ':+:' 'Nat' n) = 
  -- fastest [ 'Tct.Instances.matrix' 'Tct.Instances.defaultOptions' { dim = d } | d <- [start..start+n] ] where
  -- .
  -- withDP = 
  --   ('Tct.Instances.timeout' 5 dps 'Tct.Instances.<>' dts)
  --   'Tct.Instances.>>>' 'Tct.Instances.try' ('Tct.Instances.exhaustively' 'Tct.Instances.partitionIndependent')
  --   'Tct.Instances.>>>' 'Tct.Instances.try' 'Tct.Instances.cleanTail'
  --   'Tct.Instances.>>>' 'Tct.Instances.try' 'Tct.Instances.usableRules' where 
  --     dps = 'Tct.Instances.dependencyPairs' 'Tct.Instances.>>>' 'Tct.Instances.try' 'Tct.Instances.usableRules' 'Tct.Instances.>>>' wgOnUsable
  --     dts = 'Tct.Instances.dependencyTuples'
  --     wgOnUsable = 'Tct.Instances.weightgap' 'Tct.Instances.defaultOptions' { degree = Just 1 , on = WgOnTrs }
  -- @ 
  --  
  -- Consider the first strategy declaration that defines a strategy 
  -- @matrices [:start /<nat>/] /<nat>/@.
  -- The declaration indicates that this strategy takes two parameters, 
  -- the left and respectively right argument to the operator ':+:'.
  -- In general, the infix operator ':+:' can be used to 
  -- combine an arbitrary sequence of parameters. 
  -- In the declaration above, the defined strategy expects two natural numbers, 
  -- as indicated by the constructor 'Args.naturalArg'. 
  -- The first parameter is declared as an optional parameter called /start/, whose default
  -- value is given as @1@. 
  -- The parameters are provided to the code of @matrices@. 
  -- Using the supplied parameters /start/ and /n/, 
  -- the code evaluates to a processor that searches for /n/ different
  -- matrix interpretations of increasing dimension in parallel. 
  -- Along with other processors and combinators, both 'Tct.Instances.matrix' and 'Tct.Instances.fastest'
  -- from the module "Tct.Instances". 
  --     
  -- The second strategy declaration above declares a /transformation/
  -- called /withDP/. Transformations generate from the input problem 
  -- a possibly empty set of /sub-problems/, in a complexity preserving manner. 
  -- For every transformation /t/
  -- and processor /p/, one can use
  -- the processor @/t/ 'Tct.Instances.>>|' /p/@ 
  -- which first applies transformation /t/
  -- and then proceeds according to /p on all 
  -- resulting sub-problems.
  -- Strategy declarations perform such a lifting of transformation implicitly, 
  -- the declaration of /withDP/ for instance results in a strategy @withDP /<processor/@.
     
  -- ** Parameter Declarations
  -- | #decls#
  -- Values of type @'Arg' /a/@ can be used to define single parameters, and can be combined with ':+:' to create a parameter list.
  -- Note that the type variable /a/ accounts for the type of the defined parameter, and must be an instance of 'Tct.Processors.Args.ParsableArgument'.  
  -- In Section 'Tct.Configuration#primdecls' below we provide various instances. 
  --     
  , Arg (..)
  -- | Constructor for @'Arg' a@ with sensible defaults.    
  , arg
  , (:+:)(..)
  , optional 
    
  -- *** Primitives
  -- | #primdecls#
  
  , Args.boolArg
  , Args.naturalArg
  , Args.processorArg
  , Args.EnumArg
  , Args.AssocArg
  , Args.AssocArgument (..)      
    
  -- *** 
  -- | Argument that can additionally be /none/.
  , Args.maybeArg
  , Args.listArg
  -- only exported
  , Custom.strategy
  , Custom.Strategy (..)
  , Args.Nat (..)
  )
where

import qualified Tct.Interactive as Interactive ()
import qualified Tct.Instances as Instances ()
import Tct (defaultConfig, Config (..), tct)
import qualified Tct.Processor.Args.Instances as Args
import qualified Tct.Processor.Args as Arg ()
import Tct.Processor.Args
import qualified Tct.Method.Custom as Custom

