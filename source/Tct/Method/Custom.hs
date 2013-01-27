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
      Custom (..)
      , strategy
      , withArgs
      , SomeCode (..)        
    -- , Description (..)      
    --   -- * Constructors
    -- , fromInstance
    -- , asProcessor
    -- , fromAction
    )
where

import qualified Tct.Processor.Standard as S
import qualified Tct.Processor as P
import qualified Tct.Utils.Xml as Xml
import qualified Tct.Processor.Args as A
import Termlib.Problem (Problem)
import Termlib.Utils (underline)
import Text.PrettyPrint.HughesPJ hiding (parens)

-- | This processor allows lifting of actions and instances back to processors.
data Custom args res code = Custom { as :: String
                                   , arguments :: args
                                   , code :: code}

--------------------------------------------------------------------------------
-- processor instance

class Code code arg res | code -> res, code -> arg where
  toCode :: forall m. P.SolverM m => code -> A.Domains arg -> Problem -> m res

class GetArgs code arg | code -> arg where
  getArgs :: (Custom arg res code) -> arg
  getArgs = arguments

instance (A.Arguments arg, P.ComplexityProof res, GetArgs code arg, Code code arg res) 
         => P.Processor (Custom arg res code) where
    type ProofOf (Custom arg res code) = res
    data InstanceOf (Custom arg res code) = TP (Custom arg res code) (A.Domains arg)
    name = as
    processorToXml (TP cs args) = 
      Xml.elt "processor" [] [ Xml.elt "name" [] [Xml.text $ as cs]
                             , Xml.elt "arguments" [] $ A.toXml (getArgs cs) args
                             , Xml.elt "description" [] []]
    instanceName (TP cs _) = as cs
    solve_ (TP cs arg) prob = toCode (code cs) arg prob

instance (A.Arguments arg, P.ComplexityProof res, A.ParsableArguments arg, GetArgs code arg, Code code arg res) 
         => P.ParsableProcessor (Custom arg res code) where
    description _ = []
    synString cs = [ P.Token (as cs) , P.OptArgs] ++ [ P.PosArg i | (i,_) <- P.posArgs cs ]
    posArgs cs = zip [1..] ds
        where ds = filter (not . P.adIsOptional) (A.descriptions $ getArgs cs)
    optArgs cs = filter P.adIsOptional (A.descriptions $ getArgs cs)
    parseProcessor_ cs = do 
      args <- S.mkParseProcessor (as cs) (getArgs cs)
      return $ TP cs args
    parseFromArgsInteractive cs procs =
      do putStrLn $ show $ underline $ text "Enter arguments for processor '" <> text (as cs) <> text "':"
         putStrLn ""
         args <- A.parseInteractive (getArgs cs) procs 
         putStrLn ""
         return $ TP cs args


strategy :: Custom args res code
strategy = Custom { as = "?"
                  , arguments = undefined
                  , code = undefined }
             
----------------------------------------------------------------------
--- code instances

data SomeCode arg res = SomeCode (forall m. P.SolverM m => A.Domains arg -> Problem -> m res)

instance (P.Processor proc, ds ~ A.Domains args, proof ~ P.ProofOf proc) => Code (ds -> P.InstanceOf proc) args proof where
   toCode mkinst ds = P.solve (mkinst ds)
instance (P.Processor proc, proof ~ P.ProofOf proc) => Code (P.InstanceOf proc) A.Unit proof where
   toCode inst () = P.solve inst
instance Code (SomeCode args res) args res where 
  toCode (SomeCode f) ds = f ds

instance (P.Processor proc, ds ~ A.Domains args, proof ~ P.ProofOf proc) => GetArgs (ds -> P.InstanceOf proc) args where
instance (P.Processor proc, proof ~ P.ProofOf proc) => GetArgs (P.InstanceOf proc) A.Unit where
   getArgs _ = A.Unit
instance GetArgs (SomeCode args res) args


withArgs :: (A.Arguments arg, P.ComplexityProof res) => Custom arg res code -> A.Domains arg -> P.InstanceOf (Custom arg res code)
withArgs = TP

