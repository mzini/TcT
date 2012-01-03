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
  -- A more expressive way to configure TcT is to alter the
  -- configuration file @tct.hs@, usually residing in the directory @${HOME}\/.tct@. 
  -- The configuration file is in fact a Haskell script (<http://haskell.org>), 
  -- consequently the full expressiveness of Haskell can be used. 
  -- Note however that this option requires a 
  -- Haskell compiler to be installed on your system. 
  --
  -- In case the configuration file is missing, TcT will automatically generate
  -- the following default configuration:
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
  defaultConfig
  , tct
  
  -- * Adding Custom Processors to TcT
  -- | Defining a custom processor requires defining
  -- 
  --  (1) a /name/ for the processor, 
  --
  --  (2) a description of /arguments/ it accepts, and
  --
  --  (3) some /code/ that given a complexity problem generates a complexity proof (cf. the class 'P.ComplexityProof').
  -- 
  -- The most easy way is to define a costum processor from predefined processor, 
  -- as obtained by the constructors in module "Tct.Instances". Alternatively, 
  -- one can also specify an action that given a complexity problem, constructs 
  -- a complexity proof.
    
  , Description (..)
  , Custom.fromInstance
  , Custom.fromAction
    
  -- | 
  -- The following example defines a new processor that searches for matrix-interpretations of dimension @1@ to @3@
  -- in parallel, cf. 'Instances.matrix' and 'Instances.fastest'.  
  -- 
  -- >>> matrices = fromInstance description inst
  --      where description = Description { as    = "matrices"
  --                                      , args  = Unit
  --                                      , descr = ["Applies matrices of dimension 1 to 3 in parallel."] 
  --                                      }
  --            inst () = fastest [ matrix defaultOptions {dim = i} | i <- [1..3] ]
  --
  -- As defined by the given description, the name of this custom processor is /matrices/.
  -- A processor accepts zero or more arguments, in the above example the field 'args' of the 
  -- description states that the processor does not accept any arguments. 
  -- 
  -- To make the processor available through the command line, we add it the the processors 
  -- field of the configuration using the operator 'P.<|>' as follows:
  -- 
  -- >>> config = defaultConfig { processors = matrices <|> processors defaultConfig }
  -- 
  -- On the next startup, TcT will automatically recompile the configuration file.
  -- The above defined processor is availabe as /matrices/.
  --
  -- >>> tct --list matrices
  -- Configuration '~/.tct/tct.hs' changed. Recompiling.
  -- Program reconfiguration successful.
  -- . 
  -- Processor "matrices":
  -- ---------------------
  --   Applies matrices with dimension 1 to 3 in parallel.
  -- .  
  --   Usage:
  --    matrices
  -- 
  -- The new processor can be applied to a complexity problem using the flag '--strategy' (or '-s' for short).
  --
  -- >>> tct --strategy 'matrices' <problem-file>
  --
    
  -- ** Adding Arguments
  -- | So far, the new defined processor /matrices/ does not accept any arguments.
  -- Arguments can be specified with the field 'args' of the given 'Description'. 
  -- 
  -- As seen above, the value 'Unit' is used to specify that a processor takes no argument. 
  -- A single argument is described with a value of type @'Arg' t@. 
  -- Here the type @t@ reflects the type of the argument, for instance, 
  -- @'Arg' 'Args.Nat'@ refers to an argument which is a natural number. 
  -- In order to be used in the description of a processor, the type @t@ must be an instance of 'ParsableArgument'.
  -- Usually it is necessary 
  -- to annotate the type @t@ by providing a type signature. Alternatively, 
  -- one can use the predefined argument descriptions like 'Args.naturalArg' defined below (cf. "Tct.Configuration#predef").
  -- Use 'optional' for constructing optional arguments.
  -- Finally, use ':+:' to create tuples of arguments.
  , arg 
  , optional 
  
  -- | The next definition extends the /matrices/ processor as defined above by two arguments of type 'Args.Nat', 
  -- and one argument of type 'Bool'.
  --    
  -- >>> ms = fromInstance description inst
  --      where description = 
  --                Description { as = "matrices"
  --                            , descr = ["The processor 'matrices n' applies matrices of " 
  --                                       ++ "dimension 'startdim' to dimension 'startdim + n' in parallel."]
  --                             , args = optional "startdim" 1 naturalArg { description = "Lowest dimension." } 
  --                                      :+: 
  --                                       optional "fast" True boolArg { description = "If 'On', return certificate of fastest processor." }
  --                                      :+: 
  --                                      naturalArg
  --                             }
  --            inst (Nat sdim :+: fast :+: Nat n) = comb [ matrix defaultOptions {dim = i} | i <- [sdim..sdim+n] ]
  --                where comb | fast      = fastest
  --                           | otherwise = best    
  --  
  -- Note that the instance constructor @inst@ takes a triple of arguments, with elements separated by @:+:@. This corresponds with the 
  -- number of arguments reflected in the field 'args' of the description.
  -- The newly defined processor presents itself as follows:
  -- 
  -- >>> tct --list matrices
  -- Processor "matrices":
  -- ---------------------
  --   The processor 'matrices n' applies matrices of dimension 'startdim'
  --   to dimension 'startdim + n' in parallel.
  -- .  
  --   Usage:
  --    matrices [:startdim <nat>] [:fast On|Off] <nat>
  --   Arguments:
  --    startdim: Lowest dimension. The default is set to '1'.
  --    fast:     If 'On', return certificate of fastest processor. The default is
  --              set to 'On'.
    
  -- ** Predefined Argument Types
  -- | #predef# 
  , Unit (..)    
  , (:+:)(..)
  , Arg (..)
  , Args.boolArg
  , Args.naturalArg
  , Args.processorArg
  , Args.maybeArg
  , Args.EnumArg
  , Args.AssocArg
  , Args.AssocArgument (..)      
    
  -- * The Configuration Object
  -- | The type 'Config' reflects the configuration of 'TcT'.
  -- Notably that the field 'processors' allows adding custom defined processors to
  -- TcT. 
  -- Note that option specified at the command line will be reflected in the configuration object, 
  -- i.e. command line options overwrite the ones supplied in the config file.
    
    , Config (..)
    , (P.<|>)
  )
where

import qualified Tct.Interactive as Interactive ()
import qualified Tct.Instances as Instances
import Tct (defaultConfig, Config (..), tct)
import qualified Tct.Processor.Args.Instances as Args
import qualified Tct.Processor.Args as Arg ()
import Tct.Processor.Args
import Tct.Method.Custom (Description(..))
import qualified Tct.Processor as P
import qualified Tct.Method.Custom as Custom
