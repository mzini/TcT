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
    -- ( processor
    -- , processorArgs
    -- , TheProcessor
    -- , Processor (..))
where

import Text.ParserCombinators.Parsec

import Tct.Proof
import qualified Tct.Processor as P
import qualified Tct.Processor.Args as A
import Tct.Processor.Args hiding (name, description, synopsis)
import Termlib.Problem (Problem)

import Tct.Processor.Parse

data TheProcessor a = TheProcessor { processor     :: a
                                   , processorArgs :: Domains (ArgumentsOf a) }

class ComplexityProof (ProofOf a) => Processor a where
    type ArgumentsOf a
    type ProofOf a
    name         :: a -> String
    instanceName :: TheProcessor a -> String
    instanceName = name . processor
    description  :: a -> [String]
    description  = const []
    arguments    :: a -> (ArgumentsOf a)
    solve        :: P.SolverM m => TheProcessor a -> Problem -> m (ProofOf a)


data StdProcessor a = StdProcessor a

instance (Processor a, Arguments (ArgumentsOf a)) => P.Processor (StdProcessor a) where
    type P.ProofOf (StdProcessor a)    = ProofOf a
    data P.InstanceOf (StdProcessor a) = TP (TheProcessor a)
    name (StdProcessor a)              = name a
    instanceName (TP theproc)          = instanceName theproc
    solve_ (TP theproc) prob           = solve theproc prob

instance (Processor a, ParsableArguments (ArgumentsOf a)) => P.ParsableProcessor (StdProcessor a) where
    synopsis (StdProcessor a)        = name a ++ " " ++ A.synopsis (arguments a) 
    parseProcessor_ (StdProcessor a) = do args <- mkParseProcessor (name a) (arguments a)
                                          return $ TP $ TheProcessor { processor = a
                                                                     , processorArgs = args}
    description (StdProcessor a)     = description a
    argDescriptions (StdProcessor a) = [ (adName d, descr d) | d <- descriptions $ arguments a, adIsOptional d]
        where descr d = adDescr d ++ argDescrOnDefault mshow d
                  where mshow Nothing    = "" 
                        mshow (Just def) = " The default is set to '" ++ show def ++ "'."

mkParseProcessor :: (ParsableArguments a) => String -> a -> P.ProcessorParser (Domains a)
mkParseProcessor nm args = do _ <- try $ string nm >> whiteSpace
                              parseArguments nm args

calledWith :: Processor a => a -> Domains (ArgumentsOf a) -> P.InstanceOf (StdProcessor a)
p `calledWith` a = TP $ TheProcessor { processor = p
                                     , processorArgs = a }

