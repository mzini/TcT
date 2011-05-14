{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE ScopedTypeVariables #-}
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
    -- ( TProof (..)
    -- , subProofs
    -- , findProof
    -- , Result (..)
    -- , TheTransformer (..)
    -- , Transformer(..)
    -- , Verifiable (..)
    -- , TransformationProcessor
    -- , transformationProcessor
    -- , answerTProof
    -- , prettyPrintTProof
    -- , calledWith
    -- , enumeration
    -- , enumeration'
    -- , strict
    -- , nonstrict
    -- , sequentialSubgoals
    -- , parallelSubgoals      
    -- ) 
where

import Control.Monad (liftM)

import Data.Maybe (catMaybes)
import Termlib.Problem
import qualified Termlib.Utils as Util
import Text.PrettyPrint.HughesPJ
import Data.Typeable
import qualified Tct.Processor as P
import qualified Tct.Processor.Standard as S
import Data.Maybe (fromMaybe)
import Tct.Processor.PPrint
import qualified Tct.Processor.Args as A
import Tct.Processor.Args.Instances
import Tct.Processor.Args hiding (name, description, synopsis)

--------------------------------------------------------------------------------
--- Transformation Proofs

class TransformationProof t where
  answer :: P.Processor sub => Proof t sub -> P.Answer
  pprint :: P.Processor sub => Proof t sub -> Doc
  pprint proof = block "Transforming the problem results in the following subproblems" (P.inputProblem `mapEnum` subproofs)
                 $+$ block "Transformation Details" (enumeration' [pprintProof t input tproof])
                 $+$ details subproofs
--              $+$ pprintProof prob proof 
      where subproofs = subProofs proof
            tproof    = transformationProof proof
            t         = appliedTransformer proof
            input     = inputProblem proof
  pprintProof :: TheTransformer t -> Problem -> ProofOf t -> Doc
  continue :: TheTransformer t -> ProofOf t -> Bool
  continue _ _ = False

data Result t = NoProgress (ProofOf t)
              | Progress (ProofOf t) (Enumeration Problem)


data Proof t sub = Proof { transformationResult :: Result t  -- == Standard.ProofOf (TransProc t sub)
                         , inputProblem         :: Problem
                         , appliedTransformer   :: TheTransformer t
                         , appliedSubprocessor  :: P.InstanceOf sub
                         , subProofs            :: Enumeration (P.Proof sub) }

proofFromResult :: Result t -> (ProofOf t)
proofFromResult (NoProgress t) = t
proofFromResult (Progress t _) = t

mapResult :: (ProofOf t1 -> ProofOf t2) -> Result t1 -> Result t2
mapResult f (NoProgress p)  = NoProgress (f p)
mapResult f (Progress p ps) = Progress (f p) ps

transformationProof :: Proof t sub -> ProofOf t
transformationProof tproof = case transformationResult tproof of 
                               NoProgress p -> p
                               Progress p _ -> p
                               
subProblems :: Proof t sub -> Enumeration Problem
subProblems tproof = case transformationResult tproof of 
                       Progress _ ps -> ps
                       NoProgress _  -> []

findProof :: (Numbering a) => a -> Proof t sub -> Maybe (P.Proof sub)
findProof e p = find e (subProofs p)

-- someProof :: (Transformer t) => t -> Problem -> Result t -> Enumeration (P.Proof P.SomeProcessor) -> Proof t P.SomeProcessor
-- someProof prob res subproofs = Proof { transformationResult = res
--                                      , inputProblem         = prob
--                                      , subProofs            = subproofs }
--------------------------------------------------------------------------------
--- Transformation Class

data TheTransformer t = TheTransformer { transformation :: t
                                       , transformationArgs :: Domains (ArgumentsOf t)}


class (Arguments (ArgumentsOf t), TransformationProof t) => Transformer t where
    name         :: t -> String
    description  :: t -> [String]
    description  = const []

    type ArgumentsOf t
    type ProofOf t
    arguments    :: t -> (ArgumentsOf t)
    instanceName :: TheTransformer t -> String
    instanceName = name . transformation
    transform    :: P.SolverM m => TheTransformer t -> Problem -> m (Result t)


--------------------------------------------------------------------------------
--- Transformation Processor

data TransProc t sub = TransProc t

instance ( Transformer t 
         , P.Processor sub) 
         => S.Processor (TransProc t sub) where
    type S.ProofOf (TransProc t sub) = Proof t sub
    type S.ArgumentsOf (TransProc t sub) = Arg (Maybe Bool) :+: Arg (Maybe Bool) :+: ArgumentsOf t :+: Arg (Proc sub)
    name (TransProc t)      = name t
    description (TransProc t) = description t
    arguments (TransProc t) = opt { A.name = "strict"
                              , A.description = unlines [ "If this flag is set and the transformation fails, this processor aborts."
                                                        , "Otherwise, it applies the subprocessor on the untransformed input."] 
                              , A.defaultValue = Nothing }
                          :+: opt { A.name = "parallel"
                                  , A.description = "Decides whether the given subprocessor should be applied in parallel"
                                  , A.defaultValue = Nothing }
                          :+: arguments t 
                          :+: arg { A.name = "subprocessor"
                                  , A.description = "The processor that is applied on the transformed problem(s)" }
    solve inst prob = do res <- transform tinst prob
                         case res of 
                           NoProgress _  -> return $ mkProof res []
                           Progress _ ps -> do esubproofs <- P.evalList (toBool par) (P.succeeded . snd) 
                                                           [P.apply sub p' >>= \ r -> return (e,r) | (e,p') <- ps]
                                               return $ case mkSubproofs esubproofs ps of 
                                                           Just sps -> mkProof res sps
                                                           Nothing  -> mkProof res []
        where (TransProc t) = S.processor inst
              tinst         = TheTransformer t args
              str :+: par :+: args :+: sub = S.processorArgs inst
              toBool = maybe False id 
              mkSubproofs (Right subproofs) ps = sequence [(,) (SN e) `liftM` find e subproofs | (SN e,_) <- ps]
              mkSubproofs (Left  (fld,ss))  _  = Just (fld : ss)
              mkProof res subproofs = Proof { transformationResult = res
                                            , inputProblem         = prob
                                            , appliedSubprocessor  = sub
                                            , appliedTransformer   = tinst
                                            , subProofs            = subproofs}


instance P.Verifiable (Proof t sub)

instance ( Transformer t, P.Processor sub ) => Util.PrettyPrintable (Proof t sub) where 
  pprint proof = pprint proof

instance ( Transformer t, P.Processor sub ) => P.Answerable (Proof t sub) where 
  answer proof = answer proof

--------------------------------------------------------------------------------
--- Transformation Combinators

data t1 :>>>: t2 = TheTransformer t1 :>>>: TheTransformer t2
data ComposeProof t1 t2 = ComposeProof { firstproof :: Result t1
                                       , sndproof   :: Maybe (Enumeration (Result t2)) }


infixr 6 >>>
(>>>) :: (Transformer t1, Transformer t2) => TheTransformer t1 -> TheTransformer t2 -> TheTransformer SomeTrans
t1 >>> t2 = someTransformation inst 
    where inst = TheTransformer (t1 :>>>: t2) ()

exhaustively :: Transformer t => TheTransformer t -> TheTransformer SomeTrans
exhaustively t = t >>> try (exhaustively t)

-- data Custom res = Custom { as :: String 
--                          , code :: forall m. (P.SolverM m) => Problem -> m (res, Maybe [Problem]) }

-- instance Transformer (Custom res) where
--     name = as
--     description c = [as c]
    
--     type ArgumentsOf (Custom res) = Unit
--     type ProofOf (Custom res) = res
--     transform (TheTransformer (Custom _ code) _) prob = do (res, mprobs) <- code prob
--                                                            case mprobs of 
--                                                              Just probs -> Progress res (enumeration' prob)
--                                                              Nothing    -> NoProgress res

-- custom :: String -> (forall m. (P.SolverM m) => Problem -> m res) -> TheTransformer (Custom res)
-- custom n m = TheTransformer (Custom n m) ()


instance (Transformer t1, Transformer t2) => TransformationProof (t1 :>>>: t2) where
    pprint proof =
      case tproof of 
         ComposeProof r1 Nothing    -> pprintProof t1 input (proofFromResult r1)
         ComposeProof r1 (Just r2s) -> Util.pprint $ mkComposeProof sub t1 t2 input r1 r2s subproofs
      where tproof    = transformationProof proof
            input     = inputProblem proof
            subproofs = P.someProcessorProof `mapEnum` subProofs proof
            sub       = P.someInstance (appliedSubprocessor proof)
            TheTransformer (t1 :>>>: t2) () = appliedTransformer proof

    answer proof = 
      case tproof of 
         ComposeProof _  Nothing    -> P.MaybeAnswer
         ComposeProof r1 (Just r2s) -> answer $ mkComposeProof sub t1 t2 input r1 r2s subproofs
      where tproof    = transformationProof proof
            input     = inputProblem proof
            subproofs = P.someProcessorProof `mapEnum` subProofs proof
            sub       = P.someInstance (appliedSubprocessor proof)
            TheTransformer (t1 :>>>: t2) () = appliedTransformer proof

    pprintProof (TheTransformer (t1 :>>>: _) _)  prob (ComposeProof r1 Nothing) = 
        pprintProof t1  prob (proofFromResult r1)
    pprintProof (TheTransformer (t1 :>>>: t2) _) prob (ComposeProof r1 (Just r2s)) = 
        block' "Details first transformation" [pprintProof t1 prob (proofFromResult r1)]
        $+$ if contd then block "Details second transformation" (ppsub `map` r2s) else empty
                where contd = continue t1 (proofFromResult r1)
                      subprobs = case r1 of { Progress _ ps -> ps; _ -> enumeration' [prob] }
                      ppsub (SN i, r2_i) = ( SN i
                                           , case find i subprobs of 
                                               Just prob_i -> pprintProof t2 prob_i (proofFromResult r2_i)
                                               Nothing     -> error $ "Transformation.pprintProof (t1 :>>>: t2): subproblem " ++ show (Util.pprint (SN i)) ++ " missing" )
                           -- where pp (SN e1) prob_i = text "transformation of the following problem"
                           --                           $+$ Util.pprint prob_i 
                           --                           $+$ block' "Details" [fromMaybe (text "TRANSFORMATIONPROOF is missing") ppr2i]
                           --           where ppr2i = do r2i <- find e1 r2s
                           --                            return $ pprintProof (transformation t2) prob_i (proofFromResult r2i)

mkComposeProof :: (P.Processor sub, Transformer t1, Transformer t2) => P.InstanceOf sub -> TheTransformer t1 -> TheTransformer t2 -> Problem -> Result t1 -> [(SomeNumbering, Result t2)] -> Enumeration (P.Proof sub) -> Proof t1 (S.StdProcessor (TransProc (Try t2) sub))
mkComposeProof sub t1 t2 input r1 r2s subproofs =
    Proof { transformationResult = r1
          , inputProblem        = input
          , appliedTransformer  = t1
          , appliedSubprocessor = t2try `thenApply` sub
          , subProofs           = mkSubProof1 `map` r2s }

      where t2try = case t2 of TheTransformer t2' as -> TheTransformer (Try t2') as
            mkSubProof1 (SN i, r2_i) = (SN i, P.Proof { P.appliedProcessor = t2try `thenApply` sub
                                                       , P.inputProblem     = prob_i
                                                       , P.result           = proof_i })
                where prob_i = case r1 of 
                                 NoProgress _        -> input
                                 Progress _ subprobs -> fromMaybe (error "mkComposeProof problem not found") (find i subprobs)
                      proof_i = case r2_i of 
                                  NoProgress p2_i          -> Proof { transformationResult = NoProgress (TryProof False p2_i)
                                                                   , inputProblem         = prob_i
                                                                   , appliedTransformer   = t2try
                                                                   , appliedSubprocessor  = sub
                                                                   , subProofs            = enumeration' $ catMaybes [find (One i) subproofs] } 

                                  Progress p2_i subprobs_i -> Proof { transformationResult = Progress (TryProof True p2_i) subprobs_i
                                                                   , inputProblem         = prob_i
                                                                   , appliedTransformer   = t2try
                                                                   , appliedSubprocessor  = sub
                                                                   , subProofs            = concatMap mkSubProof2 subprobs_i }
                                      where mkSubProof2 (SN j, _) = case find (Two (i,j)) subproofs of 
                                                                      Just proof -> [(SN j, proof)]
                                                                      Nothing    -> []

                  
data Unique a = One a
              | Two a deriving (Typeable, Eq)

instance Numbering a => Numbering (Unique a) where 
    ppNumbering (One a) = ppNumbering a
    ppNumbering (Two a) = ppNumbering a

instance (Transformer t1, Transformer t2) => Transformer (t1 :>>>: t2) where
    name (t1 :>>>: t2) = take 20 (instanceName t1) ++ " >>> " ++ take 20 (instanceName t2)
    description _ = ["Implements sequencing of two transformations"]
    type ArgumentsOf (t1 :>>>: t2) = Unit
    type ProofOf (t1 :>>>: t2)    = ComposeProof t1 t2
    arguments _ = Unit
    transform inst prob = do
      r1 <- transform t1 prob
      case r1 of 
        NoProgress p1  -> if continue t1 p1 
                         then transform2 r1 (enumeration' [prob]) -- == [(1,prob)]
                         else return $ NoProgress $ ComposeProof r1 Nothing
        Progress _ ps -> transform2 r1 ps -- [(a,prob1), (b,prob2), (c,prob3)...]

        where transform2 :: P.SolverM m => Result t1 -> Enumeration Problem -> m (Result (t1 :>>>: t2))
              transform2 r1 ps = do r2s <- mapM trans ps
                                    let tproof = ComposeProof r1 $ Just [(e1,r2_i) | (e1, r2_i,_) <- r2s]
                                        esubprobs = concatMap mkSubProbs r2s
                                        anyProgress = isProgress r1 || any isProgress [r2_i | (_,r2_i,_) <- r2s]
                                        proof | anyProgress = Progress tproof esubprobs
                                              | otherwise   = NoProgress tproof
                                    return $ proof
                  where trans (e1, prob_i) = do {r2_i <- transform t2 prob_i; return (e1, r2_i, prob_i)}

                        isProgress :: Result r -> Bool
                        isProgress (Progress {})   = True
                        isProgress (NoProgress {}) = False

                        mkSubProbs (SN e1, Progress _ subprobs, _     ) = [(SN (Two (e1,e2)), subprob) | (SN e2, subprob) <- subprobs]
                        mkSubProbs (SN e1, NoProgress _       , prob_i) = [(SN (One e1), prob_i)]

              t1 :>>>: t2 = transformation inst

data Try t = Try t
data TryProof t = TryProof Bool (ProofOf t)

fromTry :: TheTransformer (Try t) -> TheTransformer t
fromTry (TheTransformer (Try t) as) = TheTransformer t as

instance TransformationProof t => TransformationProof (Try t) where
    continue _ _ = True
    pprint proof = case result of 
                      NoProgress (TryProof _ p) -> text "Transformation did not progress, reason:"
                                                  $+$ nest 1 (pprintProof (fromTry t) input p) 
                                                  $+$ block "We continue with the subprocessor" (P.result `mapEnum` subproofs)
                      Progress (TryProof _ p) _ -> pprint proof { appliedTransformer = fromTry t
                                                               , transformationResult = const p `mapResult` result }
      where t = appliedTransformer proof
            input = inputProblem proof
            subproofs = subProofs proof
            result    = transformationResult proof
    answer proof = answer $ proof { appliedTransformer   = TheTransformer t as 
                                  , transformationResult = result'}
      where TheTransformer (Try t) as = appliedTransformer proof
            result' = case transformationResult proof of 
                       Progress (TryProof _ p) ps -> Progress p ps
                       NoProgress (TryProof _ p)  -> NoProgress p

    pprintProof t prob (TryProof _ p) = pprintProof (fromTry t) prob p

instance (Transformer t) => Transformer (Try t) where
    name (Try t) = name t
    description (Try t) = description t
    type ArgumentsOf  (Try t) = ArgumentsOf t
    type ProofOf (Try t) = TryProof t
    arguments (Try t) = arguments t
    transform inst prob = mk `liftM` transform tinst prob
        where mk (Progress p ps) = Progress (TryProof True p) ps
              mk (NoProgress p)  = NoProgress (TryProof False p)
              Try t = transformation inst
              tinst = TheTransformer { transformation = t
                                     , transformationArgs = transformationArgs inst }

tryFailed :: TryProof t -> Bool
tryFailed (TryProof subProgressed _) = not subProgressed

try :: Transformer t => TheTransformer t -> TheTransformer (Try t)
try (TheTransformer t args) = TheTransformer (Try t) args

--------------------------------------------------------------------------------
-- SomeTransformation

data SomeTrans = forall t. (Transformer t) => SomeTrans t (Domains (ArgumentsOf t))
data SomeTransProof = forall t. (TransformationProof t) => SomeTransProof (TheTransformer t) (ProofOf t)

instance TransformationProof SomeTrans where
  answer proof = case transformationProof proof of 
                    SomeTransProof tinst tproof -> answer proof'  
                      where proof' = proof { transformationResult = result'
                                           , appliedTransformer = tinst }
                            result' = case transformationResult proof of 
                                        NoProgress _  -> NoProgress tproof
                                        Progress _ ps -> Progress tproof ps
  pprint proof = case transformationProof proof of 
                    SomeTransProof tinst tproof -> pprint proof'  
                      where proof' = proof { transformationResult = result'
                                           , appliedTransformer = tinst }
                            result' = case transformationResult proof of 
                                        NoProgress _  -> NoProgress tproof
                                        Progress _ ps -> Progress tproof ps
  continue _ (SomeTransProof t p) = continue t p
  pprintProof _ prob (SomeTransProof t p) = pprintProof t prob p
  

instance Transformer SomeTrans where
    name (SomeTrans t _) = name t
    description (SomeTrans t _) = description t

    type ArgumentsOf SomeTrans = Unit
    type ProofOf SomeTrans     = SomeTransProof
    arguments _ = Unit
    transform inst@(TheTransformer (SomeTrans t as) ()) prob = 
        mk `liftM` transform inst{transformation=t, transformationArgs = as} prob
        where mk (NoProgress p) = NoProgress (SomeTransProof tinst p)
              mk (Progress p ts) = Progress (SomeTransProof tinst p) ts
              tinst = TheTransformer t as

someTransformation :: (Transformer t) => TheTransformer t -> TheTransformer SomeTrans
someTransformation inst = inst { transformation     = SomeTrans (transformation inst) (transformationArgs inst)
                               , transformationArgs = ()}


calledWith :: (Transformer t) => t -> (Domains (ArgumentsOf t)) -> TheTransformer t
t `calledWith` as = TheTransformer t as 


infixr 2 `thenApply`

thenApply :: (P.Processor sub, Transformer t) => TheTransformer t -> P.InstanceOf sub -> P.InstanceOf (S.StdProcessor (TransProc t sub))
thenApply (TheTransformer t args) sub = (S.StdProcessor $ TransProc t) `S.withArgs` (Nothing :+: Nothing :+: args :+: sub)


type TransformationProcessor t sub = S.StdProcessor (TransProc t sub)

transformationProcessor :: (Arguments (ArgumentsOf t), ParsableArguments (ArgumentsOf t), Transformer t) => t -> TransformationProcessor t sub
transformationProcessor t = S.StdProcessor (TransProc t)

-- withArgs :: (Transformer t) => t -> (Domains (ArgumentsOf t)) -> TheTransformer t
-- t `withArgs` as = TheTransformer { transformation     = t
--                                  , isStrict           = False
--                                  , solveParallel      = False
--                                  , transformationArgs = as}

-- strict :: (Transformer t, S.Processor (Trans t p)) => P.InstanceOf (TransformationProcessor t p) -> P.InstanceOf (TransformationProcessor t p)
-- strict = S.modifyArguments $ \ (_ :+: par :+: as :+: sub) -> Just True :+: par :+: as :+: sub

-- nonstrict :: (Transformer t, S.Processor (Trans t p)) => P.InstanceOf (TransformationProcessor t p) -> P.InstanceOf (TransformationProcessor t p)
-- nonstrict = S.modifyArguments $ \ (_ :+: par :+: as :+: sub) -> Just False :+: par :+: as :+: sub

-- sequentialSubgoals :: (Transformer t, S.Processor (Trans t p)) => P.InstanceOf (TransformationProcessor t p) -> P.InstanceOf (TransformationProcessor t p)
-- sequentialSubgoals = S.modifyArguments $ \ (str :+: _ :+: as :+: sub) -> str :+: Just False :+: as :+: sub

-- parallelSubgoals :: (Transformer t, S.Processor (Trans t p)) => P.InstanceOf (TransformationProcessor t p) -> P.InstanceOf (TransformationProcessor t p)
-- parallelSubgoals = S.modifyArguments $ \ (str :+: _ :+: as :+: sub) -> str :+: Just True :+: as :+: sub

