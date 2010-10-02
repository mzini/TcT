{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeFamilies #-}
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

module Tct.Processor.Transformations where

import Tct.Proof 
import Termlib.Problem
import Termlib.Utils (PrettyPrintable (..))
import Text.PrettyPrint.HughesPJ
import Control.Concurrent.PFold (pfoldA, Return(..))
import Control.Monad.Trans (liftIO)

import qualified Tct.Processor as P
import qualified Tct.Processor.Standard as S
import Tct.Processor.PPrint
import qualified Tct.Processor.Args as A
import qualified Tct.Processor.Args.Instances ()
import Tct.Processor.Args hiding (name, description, synopsis)


data TProof t sub = TProof (ProofOf t) [P.Proof sub]
                  | UTProof (ProofOf t) (P.ProofOf sub)

data Result t = Failure (ProofOf t) 
              | Success (ProofOf t) [Problem]


data TheTransformer t = TheTransformer { transformation :: t
                                       , transformationArgs :: Domains (ArgumentsOf t)}

instance (P.Processor sub, PrettyPrintable (ProofOf t), ComplexityProof (P.ProofOf sub)) => PrettyPrintable (TProof t sub) where
    pprint (TProof tp ps) = block "Transformation Details" [tp]
                            $+$ text ""
                            $+$ overview ps
                            $+$ text ""
                            $+$ details ps
    pprint (UTProof tp p) = text "Transforming the input failed. We thus apply the subprocessor directly."
                            $+$ text ""
                            $+$ block "Transformation Details" [tp]
                            $+$ text ""
                            $+$ block "Application of the subprocessor" [p]

instance ( P.Processor sub
         , Answerable (TProof t sub)
         , PrettyPrintable (ProofOf t)
         , ComplexityProof (P.ProofOf sub))  => ComplexityProof (TProof t sub)

class Transformer t where
    type ArgumentsOf t
    type ProofOf t
    name         :: t -> String
    instanceName :: TheTransformer t -> String
    instanceName = name . transformation
    description  :: t -> [String]
    description  = const []
    arguments    :: t -> (ArgumentsOf t)
    transform    :: P.SolverM m => TheTransformer t -> Problem -> m (Result t)


data Trans t sub = Trans t

instance (P.Processor sub, ComplexityProof (P.ProofOf sub), Transformer t) => S.StdProcessor (Trans t sub) where
    type S.ProofOf (Trans t sub) = TProof t sub
    type S.ArgumentsOf (Trans t sub) = Arg Bool :+: Arg Bool :+: ArgumentsOf t :+: Arg (S.Processor sub)
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
                                  , A.description = "The processor that is applied on the transformed problem(s)"}
    solve inst prob = do res <- transform (TheTransformer t args) prob
                         case res of 
                           Failure p | strict    -> return $ TProof p []
                                     | otherwise -> do p' <- P.solve sub prob 
                                                       return $ UTProof p p'
                           Success p ps -> do esubproofs <- applyList par [(sub,p') | p' <- ps]
                                              case esubproofs of 
                                                Right subproofs   -> return $ TProof p subproofs
                                                Left  failedproof -> return $ TProof p [failedproof]
        where (Trans t) = S.processor inst
              strict :+: par :+: args :+: sub = S.processorArgs inst


transformationProcessor :: (Arguments (ArgumentsOf t), ParsableArguments (ArgumentsOf t), Transformer t) => t -> S.Processor (Trans t P.AnyProcessor)
transformationProcessor t = S.Processor (Trans t)

--calledWith :: Trans t -> Domains (Trans t sub) -> P.InstanceOf (Trans
-- calledWith :: (Transformer t, P.Processor sub, ComplexityProof (P.ProofOf sub)) =>
--      t -> Domains (S.ArgumentsOf (Trans t sub)) -> sub -> P.InstanceOf (S.Processor (Trans t sub))
type TransformationProcessor t = S.Processor (Trans t P.AnyProcessor)
type Transformation t sub = P.InstanceOf (S.Processor (Trans t sub))
calledWith :: (ParsableArguments (ArgumentsOf t), Transformer t, P.ComplexityProcessor sub) => 
              t
              -> (Domains (ArgumentsOf t))
              -> Bool 
              -> Bool
              -> P.InstanceOf sub
              -> Transformation t sub
t `calledWith` as = \ strict par sub -> (Trans t) `S.calledWith` (strict :+: par :+: as :+: sub)

applyList :: (P.SolverM m, Answerable (P.ProofOf proc), P.Processor proc) => Bool -> [(P.InstanceOf proc,Problem)] -> m (Either (P.Proof proc) [P.Proof proc])
applyList True ps = do actions <- sequence [ P.mkIO $ P.apply proc prob | (proc, prob) <- ps]
                       liftIO $ pfoldA comb (Right []) actions
    where comb (Right l) proof | succeeded proof = Continue $ Right $ proof : l
                               | otherwise       = Stop $ Left proof
applyList False []                 = return $ Right []
applyList False ((proc,prob) : ps) = do r <- P.apply proc prob
                                        if succeeded r
                                         then do rs <- applyList False ps
                                                 return $ case rs of {Right ls -> Right (r:ls); e -> e}
                                         else return $ Left r
