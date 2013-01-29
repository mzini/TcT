{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE TypeOperators #-}
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
      , Strategy (..)
      , withArgs
      , toProcessor
    )
where

import qualified Tct.Processor.Standard as S
import qualified Tct.Processor.Transformations as T
import qualified Tct.Processor as P
import qualified Tct.Utils.Xml as Xml
import qualified Tct.Processor.Args as A
import qualified Tct.Processor.Args.Instances as AI
-- import Tct.Method.TCombinator ((>>|))
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
      Xml.elt "processor" [] [ Xml.elt "name" [] [Xml.text $ as cs]
                             , Xml.elt "arguments" [] $ A.toXml (arguments cs) args
                             , Xml.elt "description" [] []]
    instanceName (TP cs _) = as cs
    solve_ (TP cs arg) prob = (code cs) arg prob

instance (A.Arguments arg, P.ComplexityProof res, A.ParsableArguments arg) 
         => P.ParsableProcessor (Custom arg res) where
    description _ = []
    synString cs = [ P.Token (as cs) , P.OptArgs] ++ [ P.PosArg i | (i,_) <- P.posArgs cs ]
    posArgs cs = zip [1..] ds
        where ds = filter (not . P.adIsOptional) (A.descriptions $ arguments cs)
    optArgs cs = filter P.adIsOptional (A.descriptions $ arguments cs)
    parseProcessor_ cs = do 
      args <- S.mkParseProcessor (as cs) (arguments cs)
      return $ TP cs args
    parseFromArgsInteractive cs procs =
      do putStrLn $ show $ underline $ text "Enter arguments for processor '" <> text (as cs) <> text "':"
         putStrLn ""
         args <- A.parseInteractive (arguments cs) procs 
         putStrLn ""
         return $ TP cs args



withArgs :: (A.Arguments arg, P.ComplexityProof res) => Custom arg res -> A.Domains arg -> P.InstanceOf (Custom arg res)
withArgs = TP

     

----------------------------------------------------------------------
--- strategies

data Strategy = forall a b. AsStrategy a b => a ::: b

strategy :: String -> b -> (String,b)
strategy name b = (name,b)

class AsStrategy a b | a -> b where -- FD for better error messages
  toProcessor :: a -> b -> P.SomeProcessor

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
              , code = \ (ds A.:+: proc) -> P.solve $ (mkInst ds) T.>>| proc}

-- ----------------------------------------------------------------------
-- --- code instances

-- -- somecode
-- data SomeCode arg res = SomeCode (forall m. P.SolverM m => A.Domains arg -> Problem -> m res)

-- instance Code (SomeCode args res) args res where 
--   toCode (SomeCode f) ds = f ds

-- -- processor instances
-- instance (P.Processor proc, proof ~ P.ProofOf proc) => Code (P.InstanceOf proc) A.Unit proof where
--    toCode inst () = P.solve inst

-- -- processor instance constructors
-- instance (P.Processor proc, ds ~ A.Domains args, proof ~ P.ProofOf proc) => Code (ds -> P.InstanceOf proc) args proof where
--    toCode mkinst ds = P.solve (mkinst ds)

-- -- transformation instances
-- instance (T.Transformer trans, proof ~ P.ProofOf (S.StdProcessor (T.Transformation trans P.AnyProcessor))) 
--          => Code (T.TheTransformer trans) (A.Arg AI.Processor) proof where
--   toCode inst proc = P.solve $ inst T.>>| proc

-- -- transformation instances constructors
-- instance (T.Transformer trans, ds ~ A.Domains args, proof ~ P.ProofOf (S.StdProcessor (T.Transformation trans P.AnyProcessor))) 
--          => Code (ds -> T.TheTransformer trans) (args A.:+: A.Arg AI.Processor) proof where
--    toCode inst (ds A.:+: proc) = P.solve $ inst ds T.>>| proc

