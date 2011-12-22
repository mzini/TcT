{-# LANGUAGE TypeOperators #-}
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
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}

module Tct.Processor.Timeout 
    ( timeout
    , timeoutProcessor
    , TOProof (..)
    , Timeout)
where 
import Control.Concurrent.Utils (timedKill)
import Control.Monad.Trans (liftIO)

import Tct.Processor.Args
import qualified Tct.Processor.Args as A
import qualified Tct.Processor.Standard as S
import Tct.Processor.Args.Instances hiding (Processor)
import Tct.Processor hiding (Proof, (<|>))
import Text.PrettyPrint.HughesPJ hiding (brackets)

data Timeout p = Timeout

timeout :: Processor p => Int -> (InstanceOf p) -> InstanceOf (S.StdProcessor (Timeout p))
timeout i proc = S.StdProcessor Timeout  `S.withArgs` (Nat i :+: proc)


timeoutProcessor :: S.StdProcessor (Timeout AnyProcessor)
timeoutProcessor = S.StdProcessor Timeout

toSeconds :: Int -> Double
toSeconds i = fromIntegral i / (10 ^ (6 :: Int))
-- ())


data TOProof p = TimedOut Int 
               | TOProof (ProofOf p)

instance Processor p => S.Processor (Timeout p) where 
    type S.ProofOf (Timeout p)     = TOProof p
    type S.ArgumentsOf (Timeout p) = Arg Nat :+: Arg (Proc p)
    description _                  = ["The processor either returns the result of the given processor"
                                     , " or, if the timeout elapses, aborts the computation and returns MAYBE."]
    name  Timeout                 = "timeout"
    arguments _                   = arg { A.name = "timeout"
                                        , A.description = "The timeout in seconds" }
                                    :+: 
                                    arg { A.name = "processor"
                                        , A.description = "The processor to apply with timeout"}
    instanceName tinst            = instanceName inst ++ " (timeout of " ++ show (toSeconds i) ++ " seconds)"
      where Nat i :+: inst = S.processorArgs tinst
    solve tinst prob  = 
        do io <- mkIO $ apply inst prob 
           r <- liftIO $ timedKill (i * (10^(6 :: Int))) io
           return $ case r of 
                      Just p  -> TOProof (result p)
                      Nothing -> TimedOut i
      where Nat i :+: inst = S.processorArgs tinst    
            
instance ComplexityProof (ProofOf p) => ComplexityProof (TOProof p) where
    pprintProof (TOProof p)  mde = pprintProof p mde
    pprintProof (TimedOut i) _   = text "Computation stopped due to timeout after" 
                                   <+> double (toSeconds i) 
                                   <+> text "seconds."
    answer (TOProof p)  = answer p
    answer (TimedOut _) = TimeoutAnswer
