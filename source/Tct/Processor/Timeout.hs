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

{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DeriveDataTypeable #-}

module Tct.Processor.Timeout 
    (timeout)
where 
import Control.Concurrent.Utils (timedKill)
import Control.Monad.Trans (liftIO)
import Data.Typeable

import Tct.Certificate (uncertified)
import Tct.Processor hiding (Proof)
import Tct.Processor.Proof
import Tct.Processor.SomeProcessor
import Tct.Proof
import Termlib.Utils (PrettyPrintable(..))
import Text.PrettyPrint.HughesPJ

data TimeoutProc = Timeout !Int SomeProcessor
                   deriving Typeable

timeout :: Int -> SomeProcessor -> SomeProcessor
timeout i proc = SomeProcessor $ Timeout (i * (10^(6 :: Int))) proc

toSeconds :: Int -> Double
toSeconds i = fromIntegral i / (10 ^ (6 :: Int))

data instance ProofFrom TimeoutProc = TimedOut Int 
                                    | forall p. (ComplexityProof p, PrettyPrintable p) => TOProof p

instance Proof (ProofFrom TimeoutProc) where 
    succeeded (TOProof p)  = succeeded p
    succeeded (TimedOut _) = False

instance ComplexityProof (ProofFrom TimeoutProc) where
    certificate (TOProof p) = certificate p
    certificate _           = uncertified

instance PrettyPrintable (ProofFrom TimeoutProc) where
    pprint (TOProof p)  = pprint p
    pprint (TimedOut i) = text "Computation stopped due to timeout after" <+> double (toSeconds i) <+> text "seconds"

instance Processor TimeoutProc where 
    name  i (Timeout t proc)    = name i proc ++ " [" ++ show (toSeconds t) ++ "]"
    solve (Timeout t proc) prob = do slvr <- getSatSolver
                                     r <- liftIO $ timedKill t (runSolver slvr $ apply proc prob)
                                     case r of 
                                       Just p  -> return $ TOProof $ p
                                       Nothing -> return $ TimedOut t
    

instance Answerable (ProofFrom TimeoutProc) where 
    answer (TOProof p) | succeeded p = CertAnswer $ certificate p
                       | otherwise   = FailAnswer
    answer (TimedOut _)              = TimeoutAnswer

