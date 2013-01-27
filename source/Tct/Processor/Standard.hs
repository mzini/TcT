{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

--------------------------------------------------------------------------------
-- | 
-- Module      :  Tct.Processor.Standard
-- Copyright   :  (c) Martin Avanzini <martin.avanzini@uibk.ac.at>, 
--                Georg Moser <georg.moser@uibk.ac.at>, 
--                Andreas Schnabl <andreas.schnabl@uibk.ac.at>,
-- License     :  LGPL (see COPYING)
--
-- Maintainer  :  Martin Avanzini <martin.avanzini@uibk.ac.at>
-- Stability   :  unstable
-- Portability :  unportable      
-- 
-- This module gives the infrastructure for /standard processors/.
--------------------------------------------------------------------------------   

module Tct.Processor.Standard 
       (
         -- * Defining new Processors
         -- | In order to define a new standard processor, 
         -- define an instance of 'Processor'.
         TheProcessor (..)
       , Processor (..)
       , StdProcessor (..)
       , withArgs
       , modifyArguments
       , apply
       )
where

import Text.ParserCombinators.Parsec
--import qualified Control.Exception as Ex

import qualified Tct.Processor as P
import qualified Tct.Utils.Xml as Xml
import qualified Tct.Processor.Args as A
import Tct.Processor.Args hiding (name, description)
import Termlib.Problem (Problem)
import Termlib.Utils (underline)
import Tct.Processor.Parse
import Text.PrettyPrint.HughesPJ hiding (parens)

-- | This datatype defines a specific instance of a standard processor 
data TheProcessor a = TheProcessor { processor     :: a -- ^ The processor.
                                   , processorArgs :: Domains (ArgumentsOf a) -- ^ Arguments of a processor.
                                   }

-- | The main class a processor implements.
class (P.ComplexityProof (ProofOf proc)) => Processor proc where
    -- | Unique name.  
    name         :: proc -> String
    -- | Description of the processor.    
    description  :: proc -> [String]
    description  = const []
    
    -- | Arguments of the processor, cf. "Tct.Processor.Args".
    type ArgumentsOf proc
    -- | Proof type of the transformation.        
    type ProofOf proc
    
    -- | Description of the arguments, cf. module "Tct.Processor.Args".
    arguments    :: proc -> (ArgumentsOf proc)
    
    -- | Optional name specific to instances. Defaults to the processor name.
    instanceName :: TheProcessor proc -> String    
    instanceName = name . processor

    -- | The solve method. Given an instance and a problem, it constructs
    -- a proof object. 
    solve        :: P.SolverM m => TheProcessor proc -> Problem -> m (ProofOf proc)
    
    -- | Similar to 'solve', but constructs a 'P.PartialProof'. At least all rules
    -- in the additional paramter of type 'P.SelectorExpression' should be /removed/. Per default, 
    -- this method returns 'P.PartialInapplicable'. 
    solvePartial :: P.SolverM m => TheProcessor proc -> P.SelectorExpression -> Problem -> m (P.PartialProof (ProofOf proc))
    solvePartial _ _ prob = return $ P.PartialInapplicable prob


-- ^ Provides a lifting from 'Processor' to 'P.Processor'.
data StdProcessor a = StdProcessor a

instance (Processor proc, Arguments (ArgumentsOf proc)) => P.Processor (StdProcessor proc) where
    type ProofOf (StdProcessor proc) = ProofOf proc
    data InstanceOf (StdProcessor proc) = TP (TheProcessor proc)
    
    name (StdProcessor proc) = name proc
    processorToXml (TP theproc) = 
      Xml.elt "processor" [] [ Xml.elt "name" [] [Xml.text $ name proc]
                             , Xml.elt "arguments" [] $ A.toXml (arguments proc) (processorArgs theproc) 
                             , Xml.elt "description" [] [Xml.text $ unwords $ description proc]]
        where proc = processor theproc
              
    instanceName (TP theproc) = instanceName theproc
    solve_ (TP theproc) prob = solve theproc prob
    solvePartial_ (TP theproc) stricts prob = solvePartial theproc stricts prob

instance (Processor a, ParsableArguments (ArgumentsOf a)) => P.ParsableProcessor (StdProcessor a) where
    description     (StdProcessor a) = description a
    synString     s@(StdProcessor a) = [ P.Token (name a) , P.OptArgs] ++ [ P.PosArg i | (i,_) <- P.posArgs s ]
    posArgs         (StdProcessor a) = zip [1..] ds
        where ds = filter (not . P.adIsOptional) (descriptions $ arguments a)
    optArgs         (StdProcessor a) = filter P.adIsOptional (descriptions $ arguments a)
    parseProcessor_ (StdProcessor a) = do args <- mkParseProcessor (name a) (arguments a)
                                          return $ TP $ TheProcessor { processor = a
                                                                     , processorArgs = args}
    parseFromArgsInteractive (StdProcessor a) procs =
      do putStrLn $ show $ underline $ text "Enter arguments for processor '" <> text (name a) <> text "':"
         putStrLn ""
         as <- A.parseInteractive (arguments a) procs 
         putStrLn ""
         return $ TP (TheProcessor a as)

mkParseProcessor :: (ParsableArguments a) => String -> a -> P.ProcessorParser (Domains a)
mkParseProcessor nm args = do _ <- string nm
                              nxt <- lookAhead (choice [ try anyChar
                                                      , eof >> return '\n'])
                              if continueWith nxt 
                               then whiteSpace >> parseArguments hlp args
                               else unexpected [nxt]
  where hlp = "proper arguments for processor '" ++ nm ++ "':\n  " ++ syn
        syn = nm ++ " " ++ (synopsis args)
        continueWith ' '  = True
        continueWith '\n' = True
        continueWith ')'  = True
        continueWith '\t' = True
        continueWith _    = False 

-- | Constructor for instances.
withArgs :: Processor a => (StdProcessor a) -> Domains (ArgumentsOf a) -> P.InstanceOf (StdProcessor a)
(StdProcessor p) `withArgs` a = TP $ TheProcessor { processor = p
                                                  , processorArgs = a }

-- | Modifyer for arguments of instances.
modifyArguments :: Processor a => (Domains (ArgumentsOf a) -> Domains (ArgumentsOf a)) -> (P.InstanceOf (StdProcessor a) -> P.InstanceOf (StdProcessor a))
modifyArguments f (TP (TheProcessor a args)) = TP (TheProcessor a (f args))
                                   
-- | Wrapper around 'solve', constructing a 'P.Proof'. 
apply :: (P.SolverM m, Processor p, Arguments (ArgumentsOf p)) =>
        (StdProcessor p) -> A.Domains (ArgumentsOf p) -> Problem -> m (P.Proof (StdProcessor p))
apply proc args prob = P.apply inst prob
    where inst = proc `withArgs` args

