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
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE UndecidableInstances #-}

module Tct.Processor.Standard 
    -- ( processor
    -- , processorArgs
    -- , TheProcessor
    -- , Processor (..))
where

import Text.ParserCombinators.Parsec

import qualified Tct.Processor as P
import qualified Tct.Processor.Args as A
import Tct.Processor.Args hiding (name, description, synopsis)
import Data.Typeable 
import Termlib.Problem (Problem)

import Tct.Processor.Parse

data TheProcessor a = TheProcessor { processor     :: a
                                   , processorArgs :: Domains (ArgumentsOf a) }

class StdProcessor a where
    type ArgumentsOf a
    type ProofOf a
    name         :: a -> String
    instanceName :: TheProcessor a -> String
    instanceName = name . processor
    description  :: a -> [String]
    description  = const []
    arguments    :: a -> (ArgumentsOf a)
    solve        :: TheProcessor a -> Problem -> P.SolverM (ProofOf a)


data Processor a = Processor a deriving (Typeable, Show)

instance (StdProcessor a, Arguments (ArgumentsOf a)) => P.Processor (Processor a) where
    type P.ProofOf (Processor a)    = ProofOf a
    data P.InstanceOf (Processor a) = TP (TheProcessor a)
    name (Processor a)            = name a
    instanceName (TP theproc)     = instanceName theproc
    description (Processor a)     = description a
    argDescriptions (Processor a) = [ (adName d, descr d) | d <- descriptions $ arguments a, adIsOptional d]
        where descr d = adDescr d ++ argDescrOnDefault mshow d
                  where mshow Nothing    = "" 
                        mshow (Just def) = " The default is set to '" ++ show def ++ "'."
    solve (TP theproc) prob       = solve theproc prob
--    fromInstance (TP theproc) = Processor $ processor theproc

instance (StdProcessor a, ParsableArguments (ArgumentsOf a)) => P.ParsableProcessor (Processor a) where
    synopsis (Processor a) = name a ++ " " ++ A.synopsis (arguments a) 
    parseProcessor_ (Processor a) = do _ <- try $ string (name a)
                                       whiteSpace
                                       args <- parseArguments (arguments a)
                                       return $ TP $ TheProcessor { processor = a
                                                                  , processorArgs = args}

calledWith :: StdProcessor a => a -> Domains (ArgumentsOf a) -> P.InstanceOf (Processor a)
p `calledWith` a = TP $ TheProcessor { processor = p
                                     , processorArgs = a }

