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

{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE TypeSynonymInstances #-}

module Tct.Processor
    ( SatSolver (..)
    , Processor (..)
    , Proof (..)
    , SolverM (..)

    , apply
    , mkIO
    , runSolver 
    , parseProcessor
    , minisatValue
    , getSatSolver

    , SomeProcessor
    , AnyProcessor
    , some
    , anyOf
    ) 
where

import Control.Monad.Error
import Control.Monad.Reader
import Text.ParserCombinators.Parsec (CharParser, choice, (<|>))

import qualified Qlogic.SatSolver as SatSolver
import Qlogic.SatSolver (Decoder)
import Qlogic.MiniSat (setCmd, MiniSat)

import Termlib.Problem

import Tct.Processor.Parse

type ProcessorParser a = CharParser [SomeProcessor] a 

data SolverState = SolverState SatSolver
data SatSolver = MiniSat FilePath

newtype SolverM r = S {runS :: ReaderT SolverState IO r }
    deriving (Monad, MonadIO, MonadReader SolverState)


class Processor a where
    type ProofOf a                  
    data InstanceOf a 
    name  :: a -> String
    fromInstance :: (InstanceOf a) -> a
    solve :: InstanceOf a -> Problem -> SolverM (ProofOf a)
    parseProcessor_ :: a -> ProcessorParser (InstanceOf a)


parseProcessor :: Processor a => a -> ProcessorParser (InstanceOf a)
parseProcessor a = parens parse <|> parse
    where parse = parseProcessor a

runSolver :: SolverState -> SolverM a -> IO a
runSolver slver m = runReaderT (runS m) slver

getSatSolver :: SolverM SatSolver
getSatSolver = do SolverState ss <- ask
                  return ss

mkIO :: SolverM a -> SolverM (IO a)
mkIO m = do s <- ask
            return $ runSolver s m

minisatValue :: (Decoder e a) => MiniSat () -> e -> SolverM (Maybe e)
minisatValue m e =  do slver <- getSatSolver
                       r <- liftIO $ val slver
                       case r of 
                         Right v -> return $ Just v
                         Left  _ -> return Nothing
    where val (MiniSat s) = SatSolver.value (setCmd s >> m) e 


data Proof proc = Proof { appliedProcessor :: InstanceOf proc
                        , inputProblem     :: Problem 
                        , result           :: ProofOf proc}

apply_ :: Processor proc => SolverState -> (InstanceOf proc) -> Problem -> IO (Proof proc)
apply_ slver proc prob = (runSolver slver $ solve proc prob) >>= mkProof
    where mkProof = return . Proof proc prob


apply :: Processor proc => (InstanceOf proc) -> Problem -> SolverM (Proof proc)
apply proc prob = do slver <- ask
                     liftIO $ apply_ slver proc prob


-- someprocessor
data SomeProcessor = forall p. (Processor p) => SomeProcessor p 
data SomeProof = forall p . SomeProof p
data SomeInstance = forall p . Processor p => SomeInstance p (InstanceOf p)

instance Processor SomeProcessor where
    type ProofOf    SomeProcessor = SomeProof
    data InstanceOf SomeProcessor = SPI SomeInstance
    name (SomeProcessor proc) = name proc
    solve (SPI (SomeInstance _ inst)) prob = SomeProof `liftM` solve inst prob
    fromInstance (SPI (SomeInstance proc _)) = SomeProcessor proc
    parseProcessor_ (SomeProcessor proc) = (SPI . SomeInstance proc) `liftM` parseProcessor_ proc

some :: forall p. (Processor p) => p -> SomeProcessor
some = SomeProcessor

-- oneof processor
data AnyProcessor = OO [SomeProcessor]

instance Processor AnyProcessor where
    type ProofOf AnyProcessor = ProofOf SomeProcessor
    data InstanceOf AnyProcessor = OOI (InstanceOf SomeProcessor) AnyProcessor
    name _ = "some processor"
    solve (OOI inst _) prob = solve inst prob
    fromInstance (OOI _ proc) = proc
    parseProcessor_ p@(OO ps) = do inst <- choice [ parseProcessor_ p' | p' <- ps]
                                   return $ OOI inst p

anyOf :: [SomeProcessor] -> AnyProcessor
anyOf = OO



