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
    , TOProof (..))
where 
import Control.Concurrent.Utils (timedKill)
import Control.Monad.Trans (liftIO)
import Text.Parsec.Prim

import qualified Tct.Processor.Parse as PP
import Tct.Processor.Args 
import qualified Tct.Processor.Standard as S
import Tct.Processor.Args.Instances
import Tct.Processor hiding (Proof, (<|>))
import Tct.Proof
import Termlib.Utils (PrettyPrintable(..))
import Text.PrettyPrint.HughesPJ hiding (brackets)

data Timeout p = Timeout

timeout :: Processor p => Int -> (InstanceOf p) -> InstanceOf (Timeout p)
timeout i proc = TOInstance (i * (10^(6 :: Int))) proc


timeoutProcessor :: Timeout (AnyProcessor SomeProcessor)
timeoutProcessor = Timeout

toSeconds :: Int -> Double
toSeconds i = fromIntegral i / (10 ^ (6 :: Int))

data TOProof p = TimedOut Int 
               | TOProof (ProofOf p)

instance Processor p => Processor (Timeout p) where 
    type ProofOf (Timeout p)         = TOProof p
    data InstanceOf (Timeout p)      = TOInstance !Int (InstanceOf p)
    name  Timeout                    = "timeout"
    instanceName (TOInstance i inst) = instanceName inst ++ " (timeout of " ++ show (toSeconds i) ++ " seconds)"
    solve_ (TOInstance t inst) prob  = 
        do io <- mkIO $ apply inst prob 
           r <- liftIO $ timedKill t io
           return $ case r of 
                      Just p  -> TOProof (result p)
                      Nothing -> TimedOut t
--    fromInstance (TOInstance i proc _) = Timeout i proc
    
instance ParsableProcessor (Timeout (AnyProcessor SomeProcessor)) where
    description Timeout              = ["The processor either returns the result of the given processor"
                                       , " or, if the timeout elapses, aborts the computation and returns MAYBE."]
    synString       Timeout = [ Token "[", PosArg 1, Token "]", PosArg 2]
    optArgs         Timeout = []
    posArgs         Timeout = [ (1, ArgDescr { adIsOptional = False
                                             , adName       = "timeout"
                                             , adDefault    = (Nothing :: Maybe Nat)
                                             , adDescr      = "The timeout in seconds"
                                             , adSynopsis   = domainName (Phantom :: Phantom Nat)})
                              , (2, ArgDescr { adIsOptional = False
                                             , adName       = "processor"
                                             , adDefault    = (Nothing :: Maybe (S.StdProcessor (AnyProcessor SomeProcessor)))
                                             , adDescr      = "The applied processor"
                                             , adSynopsis   = domainName (Phantom :: Phantom (S.StdProcessor (AnyProcessor SomeProcessor)))})
                              ]
    parseProcessor_ Timeout = do to <- parseTimeout
                                 i <- parseAnyProcessor
                                 return $ timeout to i
        where parseTimeout = (PP.brackets spec <?> "[<seconds>]")
              spec  = do n <-  number
                         return $ n
              number = try (PP.double >>= return . round) <|> PP.natural




instance PrettyPrintable (ProofOf p) => PrettyPrintable (TOProof p) where
    pprint (TOProof p)  = pprint p
    pprint (TimedOut i) = text "Computation stopped due to timeout after" <+> double (toSeconds i) <+> text "seconds"

instance Answerable (ProofOf p) => Answerable (TOProof p) where 
    answer (TOProof p)  = answer p
    answer (TimedOut _) = TimeoutAnswer