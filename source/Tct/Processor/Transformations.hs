{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE Rank2Types #-}
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

{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeFamilies #-}


module Tct.Processor.Transformations 
    ( TProof (..)
    , subProofs
    , findProof
    , Result (..)
    , TheTransformer (..)
    , Transformer(..)
    , Verifiable (..)
    , TransformationProcessor
    , transformationProcessor
    , answerTProof
    , prettyPrintTProof
    , calledWith
    , enumeration
    , enumeration'
    , strict
    , nonstrict
    , sequentialSubgoals
    , parallelSubgoals      
    , foo 
    ) 
where

import Control.Monad (liftM)

import Termlib.Problem
import Termlib.Utils (PrettyPrintable (..))
import Text.PrettyPrint.HughesPJ
import qualified Tct.Processor as P
import qualified Tct.Processor.Standard as S
import Data.Typeable (cast, Typeable)
import Tct.Processor.PPrint
import qualified Tct.Processor.Args as A
import Tct.Processor.Args.Instances
import Tct.Processor.Args hiding (name, description, synopsis)

data TProof t sub = TProof (ProofOf t) (Enumeration (Maybe (P.Proof sub)))
                  | UTProof (ProofOf t) (P.ProofOf sub)

data Result t = Failure (ProofOf t) 
              | Success (ProofOf t) (Enumeration Problem)


data TheTransformer t = TheTransformer { transformation :: t
                                       , transformationArgs :: Domains (ArgumentsOf t)}

subProofs :: TProof t sub -> Maybe (Enumeration (P.Proof sub))
subProofs (UTProof _ _) = Nothing
subProofs (TProof _ es) = mkSps es
    where mkSps [] = Just []
          mkSps ((n,Just e):es') = do es'' <- mkSps es'
                                      return $ (n,e) : es''
          mkSps _               = Nothing 

findProof :: (Numbering a) => a -> TProof t t1 -> Maybe (P.Proof t1)
findProof _ (UTProof _ _) = Nothing
findProof e (TProof _ ps) = find (SN e) ps >>= id

prettyPrintTProof :: ( PrettyPrintable (ProofOf t)
                    , P.Processor p
                    , P.Answerable (P.ProofOf p)
                    , PrettyPrintable (P.ProofOf p)) => TProof t p -> Doc
prettyPrintTProof p@(TProof tp _) = block' "Transformation Details" [tp]
                                    $+$ text ""
                                    $+$ (case subProofs p of
                                           Just ps' -> overview ps' $+$ text "" $+$ details ps'
                                           Nothing  -> text "Processing of at least one sub-problem did not finish. We abort. ")
prettyPrintTProof (UTProof tp p) = text "Transforming the input failed. We thus apply the subprocessor directly."
                            $+$ text ""
                            $+$ block' "Transformation Details" [tp]
                            $+$ text ""
                            $+$ block' "Application of the Sub-processor" [p]

answerTProof :: (P.Processor sub) => (ProofOf t -> Enumeration (P.Proof sub) -> P.Answer) -> TProof t sub -> P.Answer
answerTProof _ (UTProof _ sp)  = P.answer sp
answerTProof f p@(TProof tp _) = case subProofs p of 
                                   Just sps -> f tp sps
                                   _        -> P.MaybeAnswer

class Transformer t where
    name         :: t -> String
    description  :: t -> [String]
    description  = const []

    type ArgumentsOf t
    type ProofOf t
    arguments    :: t -> (ArgumentsOf t)
    instanceName :: TheTransformer t -> String
    instanceName = name . transformation
    transform    :: P.SolverM m => TheTransformer t -> Problem -> m (Result t)

data Trans t sub = Trans t deriving (Typeable)

instance ( Transformer t
         , P.Processor sub
         , P.ComplexityProof (TProof t sub)) 
    => S.Processor (Trans t sub) where
    type S.ProofOf (Trans t sub) = TProof t sub
    type S.ArgumentsOf (Trans t sub) = Arg Bool :+: Arg Bool :+: ArgumentsOf t :+: Arg (Proc sub)
    name (Trans t)      = name t
    description (Trans t) = description t
    arguments (Trans t) = opt { A.name = "strict"
                              , A.description = unlines [ "If this flag is set and the transformation fails, this processor aborts."
                                                        , "Otherwise, it applies the subprocessor on the untransformed input."] 
                              , A.defaultValue = False }
                          :+: opt { A.name = "parallel"
                                  , A.description = "Decides whether the given subprocessor should be applied in parallel"
                                  , A.defaultValue = True }
                          :+: arguments t 
                          :+: arg { A.name = "subprocessor"
                                  , A.description = "The processor that is applied on the transformed problem(s)" }
    solve inst prob = do res <- transform (TheTransformer t args) prob
                         case res of 
                           Failure p | str       -> return $ TProof p (enumeration' [])
                                     | otherwise -> UTProof p `liftM`  P.solve sub prob 
                           Success p ps -> do esubproofs <- P.evalList par (P.succeeded . snd) [P.apply sub p' >>= \ r -> return (e,r) | (e,p') <- ps]
                                              case esubproofs of 
                                                Right subproofs  -> return $ TProof p [(e, find e subproofs) | (e,_) <- ps]
                                                Left  (fld,subs) -> return $ TProof p (mapEnum Just $ fld : subs)
        where (Trans t) = S.processor inst
              str :+: par :+: args :+: sub = S.processorArgs inst



type TransformationProcessor t sub = S.StdProcessor (Trans t sub)

transformationProcessor :: (Arguments (ArgumentsOf t), ParsableArguments (ArgumentsOf t), Transformer t) => t -> TransformationProcessor t sub
transformationProcessor t = S.StdProcessor (Trans t)

calledWith :: (ParsableArguments (ArgumentsOf t), Transformer t, P.Processor sub, P.ComplexityProof (TProof t sub)) => 
              TransformationProcessor t sub
              -> (Domains (ArgumentsOf t))
              -> P.InstanceOf sub
              -> P.InstanceOf (TransformationProcessor t sub)
t `calledWith` as = \ sub -> t `S.withArgs` (False :+: False :+: as :+: sub)

strict :: (Transformer t, S.Processor (Trans t p)) => P.InstanceOf (TransformationProcessor t p) -> P.InstanceOf (TransformationProcessor t p)
strict = S.modifyArguments $ \ (_ :+: par :+: as :+: sub) -> True :+: par :+: as :+: sub

nonstrict :: (Transformer t, S.Processor (Trans t p)) => P.InstanceOf (TransformationProcessor t p) -> P.InstanceOf (TransformationProcessor t p)
nonstrict = S.modifyArguments $ \ (_ :+: par :+: as :+: sub) -> False :+: par :+: as :+: sub

sequentialSubgoals :: (Transformer t, S.Processor (Trans t p)) => P.InstanceOf (TransformationProcessor t p) -> P.InstanceOf (TransformationProcessor t p)
sequentialSubgoals = S.modifyArguments $ \ (str :+: _ :+: as :+: sub) -> str :+: False :+: as :+: sub

parallelSubgoals :: (Transformer t, S.Processor (Trans t p)) => P.InstanceOf (TransformationProcessor t p) -> P.InstanceOf (TransformationProcessor t p)
parallelSubgoals = S.modifyArguments $ \ (str :+: _ :+: as :+: sub) -> str :+: True :+: as :+: sub


-- foo :: (Typeable (P.InstanceOf (TransformationProcessor t p)), Transformer t, S.Processor (Trans t p)) => P.InstanceOf (TransformationProcessor t p) -> P.InstanceOf (TransformationProcessor t p)
foo inst = case cast inst of 
             Just (stdInst@(S.TP (S.TheProcessor  _ _))) -> strict stdInst
             Nothing                                   -> inst
-- class TransOps a where
--     str :: a -> a
--     nonstr :: a -> a
--     parl :: a -> a
--     seql :: a -> a
    
-- instance (Transformer t, S.Processor (Trans t p)) => TransOps (P.InstanceOf (TransformationProcessor t p)) where
--     str = strict
--     nonstr = nonstrict
--     parl = parallelSubgoals
--     seql = sequentialSubgoals
    
-- instance TransOps a where
--     str = id
--     nonstr = id
--     parl = id
--     seql = id

-- data a :>>>: b = a :>>>: b
-- type Composition t1 t2 sub = (P.InstanceOf sub -> P.InstanceOf (TransformationProcessor t1 sub)) 
--                              :>>>: (P.InstanceOf (TransformationProcessor t1 sub) -> P.InstanceOf (TransformationProcessor t2 (TransformationProcessor t1 sub)))
                             
-- instance (Transformer t1, Transformer t2, S.Processor (Trans t1 sub), S.Processor (Trans t2 (S.StdProcessor (Trans t1 sub)))) => TransOps (Composition t1 t2 sub) where
--     -- strict (A >>> B) = (nonstrict A >>> strict B)
--     str (t1 :>>>: t2) = t1' :>>>: t2' 
--         where t1' sub = nonstr (t1 sub)
--               t2' sub = strict (t2 sub)
--     -- nonstrict (A >>> B) = (nonstrict A >>> nonstrict B)
--     nonstr (t1 :>>>: t2) = t1' :>>>: t2' 
--         where t1' sub = nonstr (t1 sub)
--               t2' sub = nonstr (t2 sub)
--     -- par (A >>> B) = (par A >>> B)
--     parl (t1 :>>>: t2) = t1' :>>>: t2
--         where t1' sub = parl (t1 sub)
--     -- seq (A >>> B) = (seq A >>> B)
--     seql (t1 :>>>: t2) = t1' :>>>: t2
--         where t1' sub = seql (t1 sub)


class Verifiable proof where 
    verify :: Problem -> proof -> Enumeration (Maybe (P.Proof sub)) -> P.VerificationStatus
    verify _ _ _ = P.verifyUnchecked

instance ( Verifiable proof
         , P.Answerable (TProof t sub)
         , PrettyPrintable (TProof t sub)
         , P.Verifiable (P.ProofOf sub)
         , ProofOf t ~ proof)  => P.Verifiable (TProof t sub) where
    verify prob p@(TProof proof subps) = verify prob proof subps `P.andVerify` 
                                         case subProofs p of 
                                           Just sps -> P.allVerify [ P.verify (P.inputProblem pp) (P.result pp) | (_, pp) <- sps ]
                                           Nothing  -> P.verifyFail p (text "proof of transformed problem missing")
    verify prob (UTProof _ sub)  = P.verify prob sub


-- 


-- instance (Transformer t1, Transformer t2) => Transformer (Composition t1 t2 sub) where
--    name _ = "Composed Transformation"
--    description _ = ["Sequencing  t1 >>> t2 of two transformations t1, t2" ]
   
--    type ArgumentsOf (Composition t1 t2 sub) = Unit
--    type ProofOf    (Composition t1 t2 sub) = ProofOf (Trans t2 (TransformationProcessor t1 sub))
           
--    arguments _ = Unit
--    transform inst prob = undefined
     
           