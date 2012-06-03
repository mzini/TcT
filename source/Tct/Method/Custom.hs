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

{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE PolymorphicComponents #-}

module Tct.Method.Custom 
    ( 
      Custom (..)
    , Description (..)      
      -- * Constructors
    , fromInstance
    , asProcessor
    , fromAction
    )
where

import qualified Tct.Processor.Standard as S
import qualified Tct.Processor.Transformations as T
import qualified Tct.Processor as P
import qualified Tct.Processor.Args as A
import Termlib.Problem (Problem)

-- | This type covers all information necessary for parsing.
data Description args = Description { as    :: String -- ^ The name under which the processor is made accessible.
                                    , descr :: [String] -- ^ optional short description.
                                    , args  :: args -- ^ A description of the arguments the processor should understand.
                                    }

-- | This processor allows lifting of actions and instances back to processors.
data Custom arg proof res = Custom { description :: Description arg
                                   , code :: forall m. P.SolverM m => A.Domains arg -> Problem -> m res} 

--------------------------------------------------------------------------------
-- processor instance

instance (P.ComplexityProof res) => S.Processor (Custom arg a res) where
  type ProofOf (Custom arg a res)     = res
  type ArgumentsOf (Custom arg a res) = arg
  name        = as . description
  description = descr . description
  arguments   = args . description
  solve inst prob = (code p) ags prob
      where p = S.processor inst
            ags = S.processorArgs inst


instance (A.Arguments arg, T.TransformationProof t, res ~ T.Result t) => T.TransformationProof (Custom arg t res) where
  answer = T.answer
  pprintProof = T.pprintProof
  pprintTProof = T.pprintTProof
  tproofToXml = T.tproofToXml
  proofToXml = T.proofToXml
  
instance (A.Arguments arg, T.TransformationProof t, res ~ T.Result t) => T.Transformer (Custom arg t res) where
  type ProofOf (Custom arg t res) = T.ProofOf t
  type ArgumentsOf (Custom arg t res) = arg
  name = as . description
  description = descr . description
  arguments   = args . description
  transform inst prob = 
    do r <- (code t) ags prob
       case r of 
         T.Progress p ps -> return $ T.Progress p ps
         T.NoProgress p -> return $ T.NoProgress p
      where t = T.transformation inst
            ags = T.transformationArgs inst

-- | This function is similar to 'fromInstance', except that it 
-- expects a 'P.SolverM' action that directly constructs from a  
-- complexity problem a proof object 'res'.
fromAction :: P.ComplexityProof res => Description args -> (forall m. P.SolverM m => A.Domains args -> Problem -> m res) -> S.StdProcessor (Custom args a res)
fromAction d f = S.StdProcessor $ Custom {description = d, code = f }

-- | This function is used for lifting instance of processors, 
-- parameterised in some arguments, back to a processor.  
-- The arguments are according to the supplied 'Description'.
fromInstance :: (P.Processor proc) => 
             Description args -> (A.Domains args -> P.InstanceOf proc) -> S.StdProcessor (Custom args a (P.ProofOf proc))
fromInstance d mkinst = fromAction d (P.solve . mkinst) 

-- | Similar to 'fromInstance', but takes only the name and supposes no arguments.
asProcessor :: (P.Processor proc) => P.InstanceOf proc -> String -> S.StdProcessor (Custom A.Unit a (P.ProofOf proc))
proc `asProcessor` n = fromInstance d (\ () -> proc)
  where d = Description { as = n
                        , descr = []
                        , args = A.Unit}
                    