--------------------------------------------------------------------------------
-- | 
-- Module      :  Tct.Method.Custom
-- Copyright   :  (c) Martin Avanzini <martin.avanzini@uibk.ac.at>, 
--                Georg Moser <georg.moser@uibk.ac.at>, 
--                Andreas Schnabl <andreas.schnabl@uibk.ac.at>
-- License     :  LGPL (see COPYING)
--
-- Maintainer  :  Martin Avanzini <martin.avanzini@uibk.ac.at>
-- Stability   :  unstable
-- Portability :  unportable      
-- 
-- This module defines lifting of instances and actions to processors.
--------------------------------------------------------------------------------   

{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE PolymorphicComponents #-}

module Tct.Method.Custom 
    ( 
      Custom
    , Description (..)      
      -- * Constructors
    , fromInstance
    , asProcessor
    , fromAction
    )
where

import qualified Tct.Processor.Standard as S
import qualified Tct.Processor as P
import qualified Tct.Processor.Args as A
import Termlib.Problem (Problem)

-- | This type covers all information necessary for parsing.
data Description args = Description { as    :: String -- ^ The name under which the processor is made accessible.
                                    , descr :: [String] -- ^ optional short description.
                                    , args  :: args -- ^ A description of the arguments the processor should understand.
                                    }

-- | This processor allows lifting of actions and instances back to processors.
data Custom arg res = Custom { description :: Description arg
                             , code :: forall m. P.SolverM m => A.Domains arg -> Problem -> m res} 

--------------------------------------------------------------------------------
-- processor instance

instance (P.ComplexityProof res) => S.Processor (Custom arg res) where
  type ProofOf (Custom arg res)     = res
  type ArgumentsOf (Custom arg res) = arg
  name        = as . description
  description = descr . description
  arguments   = args . description
  solve inst prob = (code p) ags prob
      where p = S.processor inst
            ags = S.processorArgs inst

-- | This function is similar to 'fromInstance', except that it 
-- expects a 'P.SolverM' action that directly constructs from a  
-- complexity problem a proof object 'res'.
fromAction :: P.ComplexityProof res => Description args -> (forall m. P.SolverM m => A.Domains args -> Problem -> m res) -> S.StdProcessor (Custom args res)
fromAction d f = S.StdProcessor $ Custom {description = d, code = f }

-- | This function is used for lifting instance of processors, 
-- parameterised in some arguments, back to a processor.  
-- The arguments are according to the supplied 'Description'.
fromInstance :: (P.Processor proc) => 
             Description args -> (A.Domains args -> P.InstanceOf proc) -> S.StdProcessor (Custom args (P.ProofOf proc))
fromInstance d mkinst = fromAction d (P.solve . mkinst) 

-- | Similar to 'fromInstance', but takes only the name and supposes no arguments.
asProcessor :: (P.Processor proc) => P.InstanceOf proc -> String -> S.StdProcessor (Custom A.Unit (P.ProofOf proc))
proc `asProcessor` n = fromInstance d (\ () -> proc)
  where d = Description { as = n
                        , descr = []
                        , args = A.Unit}
                    