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
    , Transformation
    , TransformationProcessor
    , transformationProcessor
    , answerTProof
    , prettyPrintTProof
    , calledWith
    , enumeration
    , enumeration'
    ) 
where

import qualified Tct.Proof as Proof 
import Termlib.Problem
import Termlib.Utils (PrettyPrintable (..))
import Text.PrettyPrint.HughesPJ
import qualified Tct.Processor as P
import qualified Tct.Processor.Standard as S

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
                    , Proof.Answerable (P.ProofOf p)
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

answerTProof :: (P.Processor sub) => (ProofOf t -> Enumeration (P.Proof sub) -> Proof.Answer) -> TProof t sub -> Proof.Answer
answerTProof _ (UTProof _ sp)  = Proof.answer sp
answerTProof f p@(TProof tp _) = case subProofs p of 
                                   Just sps -> f tp sps
                                   _        -> Proof.MaybeAnswer

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

data Trans t sub = Trans t

instance ( Transformer t
         , P.Processor sub
         , Proof.ComplexityProof (TProof t sub)) 
    => S.Processor (Trans t sub) where
    type S.ProofOf (Trans t sub) = TProof t sub
    type S.ArgumentsOf (Trans t sub) = Arg Bool :+: Arg Bool :+: ArgumentsOf t :+: Arg (Proc sub)
    name (Trans t)      = name t
    arguments (Trans t) = opt { A.name = "strict"
                                       , A.description = unlines [ "If this flag is set and the transformation fails, this processor aborts."
                                                                 , "Otherwise, it applies the subprocessor on the untransformed input."] 
                                       , A.defaultValue = True }
                          :+: opt { A.name = "parallel"
                                  , A.description = "Decides whether the given subprocessor should be applied in parallel"
                                  , A.defaultValue = True }
                          :+: arguments t 
                          :+: arg { A.name = "subprocessor"
                                  , A.description = "The processor that is applied on the transformed problem(s)" }
    solve inst prob = do res <- transform (TheTransformer t args) prob
                         case res of 
                           Failure p | strict    -> return $ TProof p (enumeration' [])
                                     | otherwise -> do p' <- P.solve sub prob 
                                                       return $ UTProof p p'
                           Success p ps -> do esubproofs <- P.evalList par (Proof.succeeded . snd) [P.apply sub p' >>= \ r -> return (e,r) | (e,p') <- ps]
                                              case esubproofs of 
                                                Right subproofs   -> return $ TProof p [(e, find e subproofs) | (e,_) <- ps]
                                                Left  (fld,subs) -> return $ TProof p (mapEnum Just $ fld : subs)
        where (Trans t) = S.processor inst
              strict :+: par :+: args :+: sub = S.processorArgs inst



type TransformationProcessor t = S.StdProcessor (Trans t P.AnyProcessor)
type Transformation t sub = P.InstanceOf (S.StdProcessor (Trans t sub))

transformationProcessor :: (Arguments (ArgumentsOf t), ParsableArguments (ArgumentsOf t), Transformer t) => t -> TransformationProcessor t
transformationProcessor t = S.StdProcessor (Trans t)

calledWith :: (ParsableArguments (ArgumentsOf t), Transformer t, P.Processor sub, Proof.ComplexityProof (TProof t sub)) => 
              t
              -> (Domains (ArgumentsOf t))
              -> Bool 
              -> Bool
              -> P.InstanceOf sub
              -> Transformation t sub
t `calledWith` as = \ strict par sub -> (Trans t) `S.withArgs` (strict :+: par :+: as :+: sub)


class Verifiable proof where 
    verify :: Problem -> proof -> Enumeration (Maybe (P.Proof sub)) -> Proof.VerificationStatus
    verify _ _ _ = Proof.NotChecked

instance (Verifiable proof, Proof.Verifiable (P.ProofOf sub), ProofOf t ~ proof)  => Proof.Verifiable (TProof t sub) where
    verify prob p@(TProof proof subps) = verify prob proof subps `Proof.andVerify` 
                                         case subProofs p of 
                                           Just sps -> Proof.allVerify [ Proof.verify (P.inputProblem pp) (P.result pp) | (_, pp) <- sps ]
                                           Nothing  -> Proof.VerificationFail (text "proof of transformed problem missing")
    verify prob (UTProof _ sub)  = Proof.verify prob sub
