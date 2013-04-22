
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}

--------------------------------------------------------------------------------
-- | 
-- Module      :  Tct.Method.Timeout
-- Copyright   :  (c) Martin Avanzini <martin.avanzini@uibk.ac.at>, 
--                Georg Moser <georg.moser@uibk.ac.at>, 
--                Andreas Schnabl <andreas.schnabl@uibk.ac.at>,
-- License     :  LGPL (see COPYING)
--
-- Maintainer  :  Martin Avanzini <martin.avanzini@uibk.ac.at>
-- Stability   :  unstable
-- Portability :  unportable      
-- 
-- This module provides processors that may timeout.
--------------------------------------------------------------------------------   

module Tct.Method.Timeout 
    ( timeout
    , timeoutProcessor
    , TOProof (..)
    , Timeout)
where 
-- import Control.Concurrent.Utils (timedKill)
import Control.Monad.Trans (liftIO)
import qualified System.Timeout as TO

import Tct.Utils.Xml as Xml
import Tct.Processor.Args
import qualified Tct.Processor.Args as A
import qualified Tct.Processor.Standard as S
import Tct.Processor.Args.Instances hiding (Processor)
import Termlib.Utils (paragraph)
import qualified Tct.Processor as P
import Text.PrettyPrint.HughesPJ hiding (brackets)

data Timeout p = Timeout

-- | @timeout sec t@ 
-- aborts processor @t@ after @sec@ seconds.
timeout :: P.Processor p => Int -> (P.InstanceOf p) -> S.ProcessorInstance (Timeout p)
timeout i proc = S.StdProcessor Timeout  `S.withArgs` (Nat i :+: proc)


timeoutProcessor :: S.StdProcessor (Timeout P.AnyProcessor)
timeoutProcessor = S.StdProcessor Timeout


data TOProof p = TimedOut Int 
               | TOProof Int (P.ProofOf p)

instance P.Processor p => S.Processor (Timeout p) where 
    type ProofOf (Timeout p)     = TOProof p
    type ArgumentsOf (Timeout p) = Arg Nat :+: Arg (Proc p)
    description _                  = ["The processor either returns the result of the given processor"
                                     , " or, if the timeout elapses, aborts the computation and returns MAYBE."]
    name  Timeout                 = "timeout"
    arguments _                   = arg { A.name = "timeout"
                                        , A.description = "The timeout in seconds" }
                                    :+: 
                                    arg { A.name = "processor"
                                        , A.description = "The processor to apply with timeout"}
    instanceName tinst            = P.instanceName inst ++ " (timeout of " ++ show i ++ " seconds)"
      where Nat i :+: inst = S.processorArgs tinst
    solve tinst prob  = 
        do io <- P.mkIO $ P.apply inst prob 
           r <- liftIO $ TO.timeout (i * (10^(6 :: Int))) io
           return $ case r of 
                      Just p  -> TOProof i (P.result p)
                      Nothing -> TimedOut i
      where Nat i :+: inst = S.processorArgs tinst    
            
instance P.ComplexityProof (P.ProofOf p) => P.ComplexityProof (TOProof p) where
    pprintProof (TOProof _ p)  mde = P.pprintProof p mde
    pprintProof (TimedOut i) _   = 
      paragraph ("Computation stopped due to timeout after " 
                 ++ show (double (fromIntegral i)) ++ " seconds.")
    answer (TOProof _ p)  = P.answer p
    answer (TimedOut _) = P.TimeoutAnswer
    toXml (TOProof i p)   = Xml.elt "timeout" [] 
                            [Xml.elt "seconds" [] [Xml.text $ show (double (fromIntegral i))] 
                            , Xml.elt "subProof" [] [P.toXml p]]
    toXml (TimedOut i)  = Xml.elt "timeout" [] [Xml.text $ show (double (fromIntegral i))]