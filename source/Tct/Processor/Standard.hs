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

{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

module Tct.Processor.Standard 
    -- ( TheProcessor (..)
    -- , Processor (..)
    -- , StdProcessor(..)
    -- , theInstance
    -- , apply
    -- , withArgs
    -- , modifyArguments)
where

import Text.ParserCombinators.Parsec

import qualified Tct.Processor as P
import qualified Tct.Processor.Args as A
import Tct.Processor.Args hiding (name, description)
import Termlib.Problem (Problem)
import Termlib.Rule (Rule)

import Tct.Processor.Parse

data TheProcessor a = TheProcessor { processor     :: a
                                   , processorArgs :: Domains (ArgumentsOf a) }

class P.ComplexityProof (ProofOf proc) => Processor proc where
    type ArgumentsOf proc
    type ProofOf proc
    name         :: proc -> String
    instanceName :: TheProcessor proc -> String
    instanceName = name . processor
    description  :: proc -> [String]
    description  = const []
    arguments    :: proc -> (ArgumentsOf proc)
    solve        :: P.SolverM m => TheProcessor proc -> Problem -> m (ProofOf proc)
    solvePartial :: P.SolverM m => TheProcessor proc -> [Rule] -> Problem -> m (P.PartialProof (ProofOf proc))
    solvePartial _ _ prob = return $ P.PartialInapplicable prob


data StdProcessor a = StdProcessor a deriving Show


instance (Processor proc, Arguments (ArgumentsOf proc)) => P.Processor (StdProcessor proc) where
    type P.ProofOf (StdProcessor proc)      = ProofOf proc
    data P.InstanceOf (StdProcessor proc)   = TP (TheProcessor proc)
    name (StdProcessor proc)                = name proc
    instanceName (TP theproc)               = instanceName theproc
    solve_ (TP theproc) prob                = solve theproc prob
    solvePartial_ (TP theproc) stricts prob = solvePartial theproc stricts prob

theInstance :: P.InstanceOf (StdProcessor a) -> TheProcessor a
theInstance (TP a) = a

instance (Processor a, ParsableArguments (ArgumentsOf a)) => P.ParsableProcessor (StdProcessor a) where
    description     (StdProcessor a) = description a
    synString     s@(StdProcessor a) = [ P.Token (name a) , P.OptArgs] ++ [ P.PosArg i | (i,_) <- P.posArgs s ]
    posArgs         (StdProcessor a) = zip [1..] ds
        where ds = filter (not . P.adIsOptional) (descriptions $ arguments a)
    optArgs         (StdProcessor a) = filter P.adIsOptional (descriptions $ arguments a)
    parseProcessor_ (StdProcessor a) = do args <- mkParseProcessor (name a) (arguments a)
                                          return $ TP $ TheProcessor { processor = a
                                                                     , processorArgs = args}


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
        continueWith ')' = True
        continueWith '\t' = True
        continueWith _    = False 

withArgs :: Processor a => (StdProcessor a) -> Domains (ArgumentsOf a) -> P.InstanceOf (StdProcessor a)
(StdProcessor p) `withArgs` a = TP $ TheProcessor { processor = p
                                                  , processorArgs = a }

modifyArguments :: Processor a => (Domains (ArgumentsOf a) -> Domains (ArgumentsOf a)) -> (P.InstanceOf (StdProcessor a) -> P.InstanceOf (StdProcessor a))
modifyArguments f (TP (TheProcessor a args)) = TP (TheProcessor a (f args))
                                   
apply :: (P.SolverM m, Processor p, Arguments (ArgumentsOf p)) =>
        (StdProcessor p) -> A.Domains (ArgumentsOf p) -> Problem -> m (P.Proof (StdProcessor p))
apply proc args prob = P.apply inst prob
    where inst = proc `withArgs` args

