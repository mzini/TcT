{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE PolymorphicComponents #-}

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
-- This module defines lifting from processors to strategies, which can 
-- be used in the TcT configuration object to extend the list of available
-- processors, cf. Module 'Tct.Configuration'.
--------------------------------------------------------------------------------   


module Tct.Method.Custom 
    ( 
      Custom (..)
      , strategy
      , Strategy (..)
      , withArgs
      , strategyToProcessor
      , AsStrategy (..)
    )
where

import qualified Tct.Processor.Standard as S
import qualified Tct.Processor.Transformations as T
import qualified Tct.Processor as P
import qualified Tct.Utils.Xml as Xml
import qualified Tct.Processor.Args as A
import qualified Tct.Processor.Args.Instances as AI
import Termlib.Problem (Problem)
import Termlib.Utils (underline)
import Text.PrettyPrint.HughesPJ hiding (parens)


-- | This processor allows lifting of actions and instances back to processors.
data Custom args res = Custom { as :: String
                              , arguments :: args
                              , code :: forall m. P.SolverM m => A.Domains args -> Problem -> m res}

--------------------------------------------------------------------------------
-- processor instance

instance (A.Arguments arg, P.ComplexityProof res) 
         => P.Processor (Custom arg res) where
    type ProofOf (Custom arg res) = res
    data InstanceOf (Custom arg res) = TP (Custom arg res) (A.Domains arg)
    name = as
    processorToXml (TP cs args) = 
      Xml.elt "processor" [] [ Xml.elt "name" [] [Xml.text "named"]
                             , Xml.elt "arguments" [] $ A.toXml (arguments cs) args
                             , Xml.elt "description" [] [Xml.text $ as cs]]
    instanceName (TP cs _) = as cs
    solve_ (TP cs arg) prob = (code cs) arg prob

instance (A.Arguments arg, P.ComplexityProof res, A.ParsableArguments arg) 
         => P.ParsableProcessor (Custom arg res) where
    description _ = []
    synString cs = [ P.Token (as cs) , P.OptArgs] ++ [ P.PosArg i | (i,_) <- P.posArgs cs ]
    posArgs cs = zip [1..] ds
        where ds = filter (not . P.adIsOptional) (A.descriptions (arguments cs) Nothing)
    optArgs cs = filter P.adIsOptional (A.descriptions (arguments cs) Nothing)
    parseProcessor_ cs = do 
      args <- S.mkParseProcessor (as cs) (arguments cs)
      return $ TP cs args
    parseFromArgsInteractive cs procs =
      do putStrLn $ show $ underline $ text "Enter arguments for processor '" <> text (as cs) <> text "':"
         putStrLn ""
         args <- A.parseInteractive (arguments cs) procs 
         putStrLn ""
         return $ TP cs args


-- | Instantiate a custom processor with arguments
withArgs :: (A.Arguments arg, P.ComplexityProof res) => Custom arg res -> A.Domains arg -> P.InstanceOf (Custom arg res)
withArgs = TP


----------------------------------------------------------------------
--- strategies

data Strategy = forall code decl. AsStrategy code decl => code ::: decl

class AsStrategy code decl | code -> decl where
  toProcessor :: code -> decl -> P.SomeProcessor

type ConstantDeclaration = A.Unit -> (String,A.Unit)
type FunctionDeclaration args = (String, args)

instance (P.Processor proc) => AsStrategy (P.InstanceOf proc) ConstantDeclaration where 
  toProcessor inst f = P.someProcessor $ Custom { as = name 
                                                , arguments = A.Unit
                                                , code = const $ P.solve inst}
      where (name, _) = f undefined

instance (A.ParsableArguments args, P.Processor proc, ds ~ A.Domains args) 
  => AsStrategy (ds -> P.InstanceOf proc) (FunctionDeclaration args) where 
  toProcessor mkInst (name,args) = P.someProcessor $ 
       Custom { as = name 
              , arguments = args
              , code = \ ds -> P.solve (mkInst ds)}


instance (T.Transformer trans) => AsStrategy (T.TheTransformer trans) ConstantDeclaration where 
  toProcessor inst f = P.someProcessor $ Custom { as = name 
                                                , arguments = AI.processorArg
                                                , code = \ proc -> P.solve $ inst T.>>| proc}
      where (name, _) = f undefined

instance (A.ParsableArguments args, T.Transformer trans, ds ~ A.Domains args) 
  => AsStrategy (ds -> T.TheTransformer trans) (FunctionDeclaration args) where 
  toProcessor mkInst (name,args) = P.someProcessor $
       Custom { as = name 
              , arguments = args A.:+: AI.processorArg
              , code = \ (ds A.:+: proc) -> P.solve $ mkInst ds T.>>| proc}

strategy :: String -> b -> (String,b)
strategy name b = (name,b)

strategyToProcessor :: Strategy -> P.SomeProcessor 
strategyToProcessor (a ::: b) = toProcessor a b