{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
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
    ( timeout
    , TOProof (..))
where 
import Control.Concurrent.Utils (timedKill)
import Control.Monad.Trans (liftIO)

import Tct.Processor hiding (Proof)
import Tct.Proof
import Termlib.Utils (PrettyPrintable(..))
import Text.PrettyPrint.HughesPJ

data Timeout p = Timeout !Int p

timeout :: Processor p => Int -> (InstanceOf p) -> InstanceOf (Timeout p)
timeout i proc = TOInstance (i * (10^(6 :: Int))) (fromInstance proc) proc

toSeconds :: Int -> Double
toSeconds i = fromIntegral i / (10 ^ (6 :: Int))

data TOProof p = TimedOut Int 
               | TOProof (ProofOf p)

instance Processor p => Processor (Timeout p) where 
    type ProofOf (Timeout p) = TOProof p
    data InstanceOf (Timeout p) = TOInstance !Int p (InstanceOf p)
    name  (Timeout _ proc)    = name proc
    description (Timeout i proc) = description proc ++ ["The processor aborts after a timeout of " ++ show (toSeconds i) ++ " seconds."]
--    synopsis (Timeout _ proc)    = synopsis proc ++ "[<nat>]"                                   
    solve (TOInstance t _ inst) prob = do io <- mkIO $ apply inst prob 
                                          r <- liftIO $ timedKill t io
                                          return $ case r of 
                                                     Just p  -> TOProof (result p)
                                                     Nothing -> TimedOut t
    fromInstance (TOInstance i proc _) = Timeout i proc
    

instance PrettyPrintable (ProofOf p) => PrettyPrintable (TOProof p) where
    pprint (TOProof p)  = pprint p
    pprint (TimedOut i) = text "Computation stopped due to timeout after" <+> double (toSeconds i) <+> text "seconds"

instance Answerable (ProofOf p) => Answerable (TOProof p) where 
    answer (TOProof p)  = answer p
    answer (TimedOut _) = TimeoutAnswer

instance ComplexityProof (ProofOf p) => ComplexityProof (TOProof p)
