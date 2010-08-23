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
    , Erroneous 
    , Processor (..)
    , Proof (..)
    , Solver (..)
    , PartialProof (..)
    , ProofFrom

    , apply
    , applyPartial
    , runSolver 

    , toErroneous
--    , mergeErroneous

    , inapplicable
    , abortWith
    , minisatValue
    , catchFailed
    , getSatSolver
    ) 
where

import Control.Monad.Error
import Data.Typeable
import Text.PrettyPrint.HughesPJ
import Control.Monad.Reader

import qualified Qlogic.SatSolver as SatSolver
import Qlogic.SatSolver (Decoder, SatError(..))
import Qlogic.MiniSat (setCmd, MiniSat)

import Termlib.FunctionSymbol (Signature)
import Termlib.Problem
import Termlib.Trs (Trs)
import Termlib.Variable (Variables)
import Termlib.Utils

import Tct.Proof (succeeded, certificate)
import Tct.Certificate (uncertified)
import qualified Tct.Proof as P


data SatSolver = MiniSat FilePath

type ProcessorFailure = Doc

instance Error ProcessorFailure where strMsg = text

type Erroneous p = Either ProcessorFailure p

instance PrettyPrintable p => PrettyPrintable (Erroneous p) where 
    pprint (Right p') = pprint p'
    pprint (Left e)   = text "We abort due to the following reason:" $+$ nest 2 e

instance P.Proof p => P.Proof (Erroneous p) where
    succeeded (Right p') = succeeded p'
    succeeded _          = False

instance P.ComplexityProof p => P.ComplexityProof (Erroneous p) where
    certificate (Right p') = certificate p'
    certificate _          = uncertified


newtype Solver r = S {runS :: ErrorT ProcessorFailure (ReaderT SatSolver IO) r }
    deriving (Monad, MonadIO, MonadError ProcessorFailure, MonadReader SatSolver)

inapplicable :: Processor p => p -> ProcessorFailure
inapplicable _ = text "Processor is inapplicable."

runSolver :: SatSolver -> Solver a -> IO (Erroneous a)
runSolver slver m = runReaderT (runErrorT $ runS m) slver

getSatSolver :: Solver SatSolver
getSatSolver = ask

catchFailed :: Solver a -> Solver (Erroneous a)
catchFailed m = (Right `liftM` m) `catchError` (return . Left)

abortWith :: ProcessorFailure -> Solver a
abortWith = throwError

minisatValue :: (Decoder e a) => MiniSat () -> e -> Solver (Maybe e)
minisatValue m e =  do slver <- getSatSolver
                       r <- liftIO $ val slver
                       case r of 
                         Left Unsatisfiable   -> return Nothing
                         Left AssertFailed    -> abortWith $ text "sat assertion of formula failed"
                         Left (OtherError er) -> abortWith $ text "sat error" <+> text er
                         Right v              -> return $ Just v
    where val (MiniSat s) = SatSolver.value (setCmd s >> m) e 


data family ProofFrom proc

data Proof proc = Proof {appliedProcessor :: proc
                        , inputProblem    :: Problem 
                        , result          :: Erroneous (ProofFrom proc)}

data PartialProof proc = PartialProof { ppProof  :: ProofFrom proc
                                      , ppStrict :: Trs
                                      , ppVars   :: Variables
                                      , ppSig    :: Signature
                                      , ppProc   :: proc}

class (P.ComplexityProof (ProofFrom proc), Typeable proc) => Processor proc where
  name :: Int -> proc -> String

  solve :: proc -> Problem -> Solver (ProofFrom proc)
  solve _ _ = abortWith $ text "Processor not applicable for non-relative solving"

  solvePartial :: proc -> Problem -> Solver (PartialProof proc)
  solvePartial _ _ = abortWith $ text "Processor not applicable for relative solving"

toErroneous :: Proof proc -> Erroneous (ProofFrom proc)
toErroneous = result

-- mergeErroneous :: Erroneous (Proof proc) -> Proof proc
-- mergeErroneous = undefined


apply_ :: Processor proc => SatSolver -> proc -> Problem -> IO (Proof proc)
apply_ slver proc prob = (runSolver slver $ solve proc prob) >>= mkProof
    where mkProof = return . Proof proc prob

applyPartial_ :: Processor proc => SatSolver -> proc -> Problem -> IO (Erroneous (PartialProof proc))
applyPartial_ slver proc prob = (runSolver slver $ solvePartial proc prob)


apply :: Processor proc => proc -> Problem -> Solver (Proof proc)
apply proc prob = do slver <- getSatSolver
                     liftIO $ apply_ slver proc prob

applyPartial :: Processor proc => proc -> Problem -> Solver (Erroneous (PartialProof proc))
applyPartial proc prob = do slver <- getSatSolver
                            liftIO $ applyPartial_ slver proc prob





