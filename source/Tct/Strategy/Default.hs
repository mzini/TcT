{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE DeriveDataTypeable #-}
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

{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}

module Tct.Strategy.Default 
where
-- import Control.Monad (liftM)
import Termlib.Problem (Problem)
import Text.ParserCombinators.Parsec (CharParser)

import Control.Monad.Reader

type ProcessorParser a = CharParser [SomeProcessor] a 

-- Processor 
data SolverState = MiniSat FilePath
newtype SolverM r = S {runS :: ReaderT SolverState IO r }
    deriving (Monad, MonadIO, MonadReader SolverState)


class Processor a where
    type Proof a                  
    data Instance a 
    name  :: a -> String
    solve :: Instance a -> Problem -> SolverM (Proof a)
    parseProcessor :: a -> ProcessorParser (Instance a)


-- someprocessor

data SomeProcessor = forall p. (Processor p) => SomeProcessor p

data SomeProof = forall p . SomeProof p
data SomeInstance = forall p . Processor p => SomeInstance (Instance p)

instance Processor SomeProcessor where
    type Proof SomeProcessor = SomeProof
    data Instance SomeProcessor = I SomeInstance
    name (SomeProcessor proc) = name proc
    solve (I (SomeInstance proc)) prob = SomeProof `liftM` solve proc prob
    parseProcessor (SomeProcessor proc) = (I . SomeInstance) `liftM` parseProcessor proc

                    


