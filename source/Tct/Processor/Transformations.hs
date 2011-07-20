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
import Text.PrettyPrint.HughesPJ hiding (empty, (<>))
import qualified Text.PrettyPrint.HughesPJ as PP
import Data.Typeable
import qualified Data.Set as Set
import Data.Maybe (fromMaybe)
import Data.List (partition)

import Termlib.Problem
import qualified Termlib.Trs as Trs
import qualified Termlib.Utils as Util

import Tct.Processor.PPrint
import qualified Tct.Processor as P
import qualified Tct.Processor.Standard as S
import qualified Tct.Processor.Args as A
import Tct.Processor.Args.Instances
import Tct.Processor.Args hiding (name, description, synopsis)

--------------------------------------------------------------------------------
--- Transformation Proofs

class TransformationProof t where
  answer :: P.Processor sub => Proof t sub -> P.Answer
  pprintTProof :: TheTransformer t -> Problem -> ProofOf t -> Doc
  pprintProof :: P.Processor sub => Proof t sub -> P.PPMode -> Doc
  pprintProof proof mde = 
      pprintTProof t input tproof
      $+$ text ""
      $+$ case subprobs of 
            []   -> text "No subproblems were generated"
            [_]  -> ppDetails Nothing
            _    -> ppOverviews
                   $+$ text ""
                   $+$ ppDetails (Just "Proofs for generated problems")
      where subproofs = subProofs proof
            subprobs  = subProblems proof
            tproof    = transformationProof proof
            t         = appliedTransformer proof
            input     = inputProblem proof
            ppOverviews = text "Overall, the transformation results in the following sub-problem(s):"
                          $+$ text ""
                          $+$ block "Generated new problems" (ppOverview `map` subprobs)
            ppOverview (sn@(SN i), prob_i) = (sn, ppProb prob_i (findProof i proof))
            ppDetails mheading = case subproofs of 
                                   [] -> text "No subproblems were checked."
                                   _  -> maybe (vcat . map snd) block mheading $ ppDetail `map` subproofs
            ppDetail (i,proof_i) = (i,P.pprintProof proof_i mde)
            ppProb prob_i Nothing =  
                Util.pprint prob_i                                                               
            ppProb prob_i (Just proof_i) =  
                Util.pprint prob_i                                                               
                $+$ text ""
                $+$ (text "This problem" 
                     <+> (if P.succeeded proof_i
                           then text "was proven" <+> Util.pprint (P.answer proof_i)
                           else text "remains open")
                     PP.<> text ".")

data Result t = NoProgress (ProofOf t)
              | Progress (ProofOf t) (Enumeration Problem)



data MaybeSubsumed proof = MaybeSubsumed (Maybe Problem) proof

  
data Proof t sub = Proof { transformationResult :: Result t
                         , inputProblem         :: Problem
                         , appliedTransformer   :: TheTransformer t
                         , appliedSubprocessor  :: P.InstanceOf sub
                         , subProofs            :: Enumeration (P.Proof sub) }



answerFromSubProof :: (P.Processor sub) => Proof t sub -> P.Answer
answerFromSubProof proof = case subProofs proof of 
                              [(_, subproof)] -> P.answer subproof
                              _               -> P.MaybeAnswer


proofFromResult :: Result t -> (ProofOf t)
proofFromResult (NoProgress t) = t
proofFromResult (Progress t _) = t

isProgressResult :: Result r -> Bool
isProgressResult (Progress {})   = True
isProgressResult (NoProgress {}) = False

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
    continue :: TheTransformer t -> Bool
    continue _ = False


--------------------------------------------------------------------------------
--- Transformation Processor

subsumes :: Problem -> Problem -> Bool
p1 `subsumes` p2 = check strictTrs 
                   && check strictDPs 
                   && check trsComponents
                   && check dpComponents 
  where -- checkStr f = toSet (f p2) `Set.isProperSubsetOf` toSet (f p1)
        check f = toSet (f p2) `Set.isSubsetOf` toSet (f p1)
        toSet = Set.fromList . Trs.rules
        

data TransProc t sub = TransProc t

instance ( Transformer t 
         , P.Processor sub) 
         => S.Processor (TransProc t sub) where
    type S.ProofOf (TransProc t sub) = Proof t (Subsumed sub)
    type S.ArgumentsOf (TransProc t sub) = Arg Bool :+: Arg Bool :+: Arg Bool :+: ArgumentsOf t :+: Arg (Proc sub)
    name (TransProc t)      = name t
    instanceName inst       = instanceName tinst
        where _ :+: _ :+: _ :+: as :+: _ = S.processorArgs inst
              TransProc t          = S.processor inst
              tinst = TheTransformer t as

    description (TransProc t) = description t
    arguments (TransProc t) = opt { A.name = "strict"
                              , A.description = unlines [ "If this flag is set and the transformation fails, this processor aborts."
                                                        , "Otherwise, it applies the subprocessor on the untransformed input."] 
                              , A.defaultValue = False }
                          :+: opt { A.name = "parallel"
                                  , A.description = "Decides whether the given subprocessor should be applied in parallel"
                                  , A.defaultValue = False }
                          :+: opt { A.name = "checkSubsumed"
                                  , A.description = unlines [ "This flag determines whether the processor should reuse proofs in case that one generated problem subsumes another one."
                                                            , "A problem 'p1' is subsumed by problem 'p2' if the complexity of 'p1' is bounded from above by the complexity of 'p2'."
                                                            , "Currently we only take subset-inclusions of the different components into account" ]
                                                    
                                  , A.defaultValue = False }
                          :+: arguments t 
                          :+: arg { A.name = "subprocessor"
                                  , A.description = "The processor that is applied on the transformed problem(s)" }
    solve inst prob = do res <- transform tinst prob
                         case res of 
                           NoProgress _  -> if continue tinst || not str
                                             then do sp <- P.apply sub prob
                                                     return $ mkProof res (enumeration' [liftMS Nothing sp])
                                             else return $ mkProof res []
                           Progress _ ps -> do let (subsumed, unsubsumed) | checkSubsume = splitSubsumed ps
                                                                          | otherwise    = ([], ps)
                                               esubproofs <- P.evalList par (P.succeeded . snd) 
                                                           [P.apply sub p' >>= \ r -> return (e,r) | (e,p') <- unsubsumed]
                                               return $ case mkSubproofs esubproofs ps of 
                                                           Just sps -> mkProof res $ unsubsumedProofs ++ subsumedProofs
                                                              where unsubsumedProofs = mapEnum (liftMS Nothing) sps
                                                                    subsumedProofs = catMaybes [ do proof_i <- find e_i sps
                                                                                                    return $ (SN e_j, liftMS (Just p_i) proof_i)
                                                                                               | (SN e_i, p_i, SN e_j) <- subsumed ]

                                                           Nothing  -> mkProof res []
        where (TransProc t) = S.processor inst
              tinst         = TheTransformer t args
              str :+: par :+: checkSubsume :+: args :+: sub = S.processorArgs inst
              splitSubsumed [] = ([],[])
              splitSubsumed ((e_i, p_i):ps) = ([ (e_i, p_i, e_j) | (e_j, _) <- subs_i ] ++ subs', unsubs')
                where (subs_i, unsubs_i) = partition (\ (_, p_j) -> p_i `subsumes` p_j) ps
                      (subs', unsubs') = splitSubsumed unsubs_i
              mkSubproofs (Right subproofs) ps = sequence [(,) (SN e) `liftM` find e subproofs | (SN e,_) <- ps]
              mkSubproofs (Left  (fld,ss))  _  = Just (fld : ss)
              mkProof res subproofs = Proof { transformationResult = res
                                            , inputProblem         = prob
                                            , appliedSubprocessor  = (SSI sub)
                                            , appliedTransformer   = tinst
                                            , subProofs            = subproofs}


instance ( Transformer t, P.Processor sub ) => P.ComplexityProof (Proof t sub) where 
  pprintProof proof mde = pprintProof proof mde
  answer proof = answer proof

type TransformationProcessor t sub = S.StdProcessor (TransProc t sub)

--------------------------------------------------------------------------------
--- Transformation Combinators

data t1 :>>>: t2 = TheTransformer t1 :>>>: TheTransformer t2
data ComposeProof t1 t2 = ComposeProof { firstproof :: Result t1
                                       , sndproof   :: Maybe (Enumeration (Result t2)) }


instance (Transformer t1, Transformer t2) => TransformationProof (t1 :>>>: t2) where
    pprintProof proof mde =
      case tproof of 
         ComposeProof r1 Nothing    -> pprintTProof t1 input (proofFromResult r1)
         ComposeProof r1 (Just r2s) -> P.pprintProof (mkComposeProof sub t1 t2 input r1 r2s subproofs) mde
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

    pprintTProof (TheTransformer (t1 :>>>: _) _)  prob (ComposeProof r1 Nothing) = 
        pprintTProof t1  prob (proofFromResult r1)
    pprintTProof (TheTransformer (t1 :>>>: t2) _) prob (ComposeProof r1 (Just r2s)) = 
        pprintTProof t1 prob (proofFromResult r1)
        $+$ if not contd 
             then PP.empty 
             else text ""
                  $+$ (text "We apply the transformation" <+> Util.qtext (instanceName t2) <+> text "on the resulting sub-problems:")
                  $+$ vcat [ ppOverview i prob_i | (i, prob_i) <- subprobs]
                where contd = continue t1 || (case r1 of {Progress {} -> True; _ -> False})
                      subprobs = case r1 of { Progress _ ps -> ps; _ -> enumeration' [prob] }
                      ppOverview (SN i) prob_i = 
                          block' n [ text "We consider the problem"
                                    $+$ text ""
                                    $+$ Util.pprint prob_i
                                    $+$ text ""
                                    $+$ case find i r2s of 
                                          Nothing   -> text "We abort on this problem. THIS SHOULD NOT HAPPEN!"
                                          Just r2_i@(Progress _ ps) -> 
                                              pprintTProof t2 prob (proofFromResult r2_i)
                                              $+$ if null ps 
                                                   then PP.empty
                                                   else text ""
                                                        $+$ text "The consider problem is replaced by"
                                                        $+$ enum ps
                                          Just r2_i@(NoProgress _) -> 
                                              pprintTProof t2 prob (proofFromResult r2_i) ]
                              where n = show $ text "Sub-problem" <+> Util.pprint (SN i)

someProof :: (Transformer t, P.Processor sub) => P.InstanceOf sub -> TheTransformer t -> Problem -> Result t -> Enumeration (P.Proof sub) -> Proof t P.SomeProcessor
someProof sub t prob res subproofs = Proof { transformationResult = res
                                           , inputProblem         = prob
                                           , appliedTransformer   = t
                                           , appliedSubprocessor  = P.someInstance sub
                                           , subProofs            = (P.someProofNode sub prob . P.result) `mapEnum` subproofs }

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
                                  NoProgress p2_i          -> Proof { transformationResult = NoProgress (TryProof p2_i)
                                                                   , inputProblem         = prob_i
                                                                   , appliedTransformer   = t2try
                                                                   , appliedSubprocessor  = SSI sub
                                                                   , subProofs            = enumeration' $ catMaybes [liftMS Nothing `liftM` find (One i) subproofs] } 

                                  Progress p2_i subprobs_i -> Proof { transformationResult = Progress (TryProof p2_i) subprobs_i
                                                                   , inputProblem         = prob_i
                                                                   , appliedTransformer   = t2try
                                                                   , appliedSubprocessor  = SSI sub
                                                                   , subProofs            = concatMap mkSubProof2 subprobs_i }
                                      where mkSubProof2 (SN j, _) = case find (Two (i,j)) subproofs of 
                                                                      Just proof -> [(SN j, liftMS Nothing proof)]
                                                                      Nothing    -> []

                  
data Unique a = One a
              | Two a deriving (Typeable, Eq)

instance Numbering a => Numbering (Unique a) where 
    ppNumbering (One a) = ppNumbering a
    ppNumbering (Two a) = ppNumbering a

instance (Transformer t1, Transformer t2) => Transformer (t1 :>>>: t2) where
    name (TheTransformer t1 _ :>>>: _) = name t1
    instanceName (TheTransformer (t1 :>>>: _) _) = instanceName t1 ++ " >>> ..."
    description _ = ["Implements sequencing of two transformations"]
    type ArgumentsOf (t1 :>>>: t2) = Unit
    type ProofOf (t1 :>>>: t2)    = ComposeProof t1 t2
    arguments _ = Unit
    transform inst prob = do
      r1 <- transform t1 prob
      case r1 of 
        NoProgress _   -> if continue t1
                         then transform2 r1 (enumeration' [prob]) -- == [(1,prob)]
                         else return $ NoProgress $ ComposeProof r1 Nothing
        Progress _ ps -> transform2 r1 ps -- [(a,prob1), (b,prob2), (c,prob3)...]

        where transform2 :: P.SolverM m => Result t1 -> Enumeration Problem -> m (Result (t1 :>>>: t2))
              transform2 r1 ps = do r2s <- mapM trans ps
                                    let tproof = ComposeProof r1 $ Just [(e1,r2_i) | (e1, r2_i,_) <- r2s]
                                        esubprobs = concatMap mkSubProbs r2s
                                        anyProgress = isProgressResult r1 || any isProgressResult [r2_i | (_,r2_i,_) <- r2s]
                                        proof | anyProgress = Progress tproof esubprobs
                                              | otherwise   = NoProgress tproof
                                    return $ proof
                  where trans (e1, prob_i) = do {r2_i <- transform t2 prob_i; return (e1, r2_i, prob_i)}

                        mkSubProbs (SN e1, Progress _ subprobs, _     ) = [(SN (Two (e1,e2)), subprob) | (SN e2, subprob) <- subprobs]
                        mkSubProbs (SN e1, NoProgress _       , prob_i) = [(SN (One e1), prob_i)]

              t1 :>>>: t2 = transformation inst

--------------------------------------------------------------------------------
-- Choice
              
data Id = Id

data IdProof = IdProof

instance TransformationProof Id where
  pprintTProof _ _ _ = PP.empty
  answer = answerFromSubProof
  
instance Transformer Id where 
  name Id = "id"
  description Id = []
  type ArgumentsOf Id = Unit
  type ProofOf Id     = IdProof
  arguments Id = Unit
  transform _ _ = return $ NoProgress IdProof

--------------------------------------------------------------------------------
-- Choice
              
data t1 :<>: t2 = TheTransformer t1 :<>: TheTransformer t2

data ChoiceProof t1 t2 = ChoiceOne (Result t1)
                       | ChoiceTwo (Result t1) (Result t2)
                       
instance (Transformer t1, Transformer t2) => TransformationProof (t1 :<>: t2) where
  pprintTProof (TheTransformer (t1 :<>: _) _) prob (ChoiceOne r1) = 
    pprintTProof t1 prob (proofFromResult r1)
  pprintTProof (TheTransformer (t1 :<>: t2) _) prob (ChoiceTwo r1 r2) = 
    text "We fail transforming the problem using" <+> quotes (text (instanceName t1))
    $+$ text ""
    $+$ indent (pprintTProof t1 prob (proofFromResult r1))
    $+$ text ""
    $+$ text "We try instead" <+> quotes (text (instanceName t2)) <+> text "on the problem"
    $+$ text ""    
    $+$ Util.pprint prob
    $+$ text ""
    $+$ indent (pprintTProof t2 prob (proofFromResult r2))
    
  answer proof = case transformationProof proof of 
                    ChoiceOne r1 -> answer $ proof { transformationResult = r1 
                                                   , appliedTransformer   = t1}
                    ChoiceTwo _ r2 -> answer $ proof { transformationResult = r2, appliedTransformer   = t2}
                      
    where (TheTransformer (t1 :<>: t2) _) = appliedTransformer proof
    


instance (Transformer t1, Transformer t2) => Transformer (t1 :<>: t2) where
  name (TheTransformer t1 _ :<>: _)           = name t1
  instanceName (TheTransformer (t1 :<>: _) _) = instanceName t1 ++ " <> ..."
  
  type ArgumentsOf (t1 :<>: t2) = Unit
  type ProofOf (t1 :<>: t2) = ChoiceProof t1 t2
  arguments _ = Unit
  
  transform tinst prob = do r1 <- transform t1 prob
                            case r1 of 
                              Progress _ ps -> return $ Progress (ChoiceOne r1) ps
                              NoProgress _  -> do r2 <- transform t2 prob
                                                  return $ case r2 of 
                                                             Progress _ ps -> Progress (ChoiceTwo r1 r2) ps
                                                             NoProgress _  -> NoProgress (ChoiceTwo r1 r2)
    where t1 :<>: t2 = transformation tinst

  
--------------------------------------------------------------------------------
-- Try Transformation

data Try t = Try t
data TryProof t = TryProof (ProofOf t)

fromTry :: TheTransformer (Try t) -> TheTransformer t
fromTry (TheTransformer (Try t) as) = TheTransformer t as


instance TransformationProof t => TransformationProof (Try t) where
    pprintProof proof mde = 
        case result of 
          NoProgress (TryProof p) 
              | mde == P.ProofOutput -> ppsub
              | otherwise -> 
                  pprintTProof t' (inputProblem proof) p
                  $+$ text ""
                  $+$ text "We abort the transformation and continue with the subprocessor on the previous problem" 
                  $+$ text ""
                  $+$ Util.pprint (inputProblem proof)
                  $+$ text ""
                  $+$ ppsub
          Progress (TryProof p) _ -> pprintProof proof { appliedTransformer  = t'
                                                      , transformationResult = const p `mapResult` result } mde
      where t         = appliedTransformer proof
            t'        = fromTry t
            msubproof = case subProofs proof of 
                          [(_,sp)] -> Just sp
                          _        -> Nothing
            result    = transformationResult proof
            ppsub = case msubproof of 
                      Just sp -> P.pprintProof sp mde
                      Nothing -> text "No further proof was generated, we abort!"
    answer proof = 
        case transformationResult proof of 
          Progress (TryProof p) ps -> answer $ proof { appliedTransformer   = fromTry t
                                                    , transformationResult = Progress p ps}
          NoProgress (TryProof _)  -> case subProofs proof of 
                                       [(_,subproof)] -> P.answer subproof
                                       _              -> P.MaybeAnswer
      where t = appliedTransformer proof

    pprintTProof t prob (TryProof p) = pprintTProof (fromTry t) prob p



instance (Transformer t) => Transformer (Try t) where
    name (Try t) = name t
    continue _ = True
    instanceName inst = instanceName $ fromTry inst
    description (Try t) = description t
    type ArgumentsOf  (Try t) = ArgumentsOf t
    type ProofOf (Try t) = TryProof t
    arguments (Try t) = arguments t
    transform inst prob = mk `liftM` transform tinst prob
        where mk (Progress p ps) = Progress (TryProof p) ps
              mk (NoProgress p)  = NoProgress (TryProof p)
              Try t = transformation inst
              tinst = TheTransformer { transformation = t
                                     , transformationArgs = transformationArgs inst }

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
  pprintProof proof mde = case transformationProof proof of 
                            SomeTransProof tinst tproof -> pprintProof proof' mde
                                       where proof' = proof { transformationResult = result'
                                                            , appliedTransformer = tinst }
                                             result' = case transformationResult proof of 
                                                         NoProgress _  -> NoProgress tproof
                                                         Progress _ ps -> Progress tproof ps
  pprintTProof _ prob (SomeTransProof t p) = pprintTProof t prob p
  

instance Transformer SomeTrans where
    name (SomeTrans t _) = name t
    continue (TheTransformer (SomeTrans t as)  _) = continue (TheTransformer t as)
    
    instanceName (TheTransformer (SomeTrans t as)  _) = instanceName (TheTransformer t as)
    description (SomeTrans t _) = description t

    type ArgumentsOf SomeTrans = Unit
    type ProofOf SomeTrans     = SomeTransProof
    arguments _ = Unit
    transform inst@(TheTransformer (SomeTrans t as) ()) prob = 
        mk `liftM` transform inst{transformation=t, transformationArgs = as} prob
        where mk (NoProgress p) = NoProgress (SomeTransProof tinst p)
              mk (Progress p ts) = Progress (SomeTransProof tinst p) ts
              tinst = TheTransformer t as





-------------------------------------------------------------------------------- 
--- utility functions for constructing and modifying transformations

calledWith :: (Transformer t) => t -> (Domains (ArgumentsOf t)) -> TheTransformer t
t `calledWith` as = TheTransformer t as 

someTransformation :: (Transformer t) => TheTransformer t -> TheTransformer SomeTrans
someTransformation inst = inst { transformation     = SomeTrans (transformation inst) (transformationArgs inst)
                               , transformationArgs = ()}



infixr 2 `thenApply`
thenApply :: (P.Processor sub, Transformer t) => TheTransformer t -> P.InstanceOf sub -> P.InstanceOf (S.StdProcessor (TransProc t sub))
thenApply ti@(TheTransformer t args) sub = (S.StdProcessor $ TransProc t) `S.withArgs` (not (continue ti) :+: False :+: False :+: args :+: sub)

infixr 2 >>|
(>>|) :: (P.Processor sub, Transformer t) => TheTransformer t -> P.InstanceOf sub -> P.InstanceOf (S.StdProcessor (TransProc t sub))
(>>|) = thenApply


infixr 2 `thenApplyPar`
thenApplyPar :: (P.Processor sub, Transformer t) => TheTransformer t -> P.InstanceOf sub -> P.InstanceOf (S.StdProcessor (TransProc t sub))
thenApplyPar ti@(TheTransformer t args) sub = (S.StdProcessor $ TransProc t) `S.withArgs` (not (continue ti) :+: True :+: False :+: args :+: sub)


infixr 2 >>||
(>>||) :: (P.Processor sub, Transformer t) => TheTransformer t -> P.InstanceOf sub -> P.InstanceOf (S.StdProcessor (TransProc t sub))
(>>||) = thenApplyPar


transformationProcessor :: (Arguments (ArgumentsOf t), ParsableArguments (ArgumentsOf t), Transformer t) => t -> TransformationProcessor t sub
transformationProcessor t = S.StdProcessor (TransProc t)

parallelSubgoals :: (P.Processor p, Transformer t) => P.InstanceOf (TransformationProcessor t p) -> P.InstanceOf (TransformationProcessor t p)
parallelSubgoals = S.modifyArguments $ \ (str :+: _ :+: subs :+: as :+: sub) -> str :+: True :+: subs :+: as :+: sub

--- utility functions for constructing and modifying transformations

checkSubsumed :: (P.Processor p, Transformer t) => P.InstanceOf (TransformationProcessor t p) -> P.InstanceOf (TransformationProcessor t p)
checkSubsumed = S.modifyArguments $ \ (str :+: par :+: _ :+: as :+: sub) -> str :+: par :+: True :+: as :+: sub


try :: Transformer t => TheTransformer t -> TheTransformer (Try t)
try (TheTransformer t args) = TheTransformer (Try t) args

infixr 6 >>>
(>>>) :: (Transformer t1, Transformer t2) => TheTransformer t1 -> TheTransformer t2 -> TheTransformer SomeTrans
t1 >>> t2 = someTransformation inst 
    where inst = TheTransformer (t1 :>>>: t2) ()


infixr 7 <>
(<>) :: (Transformer t1, Transformer t2) => TheTransformer t1 -> TheTransformer t2 -> TheTransformer SomeTrans
t1 <> t2 = someTransformation inst 
    where inst = TheTransformer (t1 :<>: t2) ()

exhaustively :: Transformer t => TheTransformer t -> TheTransformer SomeTrans
exhaustively t = t >>> exhaustively t


idtrans :: TheTransformer Id
idtrans = Id `calledWith` ()

-------------------------------------------------------------------------------- 
--- subsumed processor
data Subsumed sub = Subsumed sub

liftMS :: Maybe Problem -> P.Proof proc -> P.Proof (Subsumed proc)
liftMS mprob proof = proof { P.appliedProcessor = SSI (P.appliedProcessor proof)
                           , P.result           = MaybeSubsumed mprob (P.result proof) }

instance P.ComplexityProof proof => P.ComplexityProof (MaybeSubsumed proof) where 
  answer (MaybeSubsumed _ proof) = P.answer proof
  pprintProof (MaybeSubsumed Nothing  proof) mde = P.pprintProof proof mde
  pprintProof (MaybeSubsumed (Just p) proof) mde = text "The complexity of the input problem is bounded by the complexity of the problem"
                                                   $+$ text ""
                                                   $+$ indent (Util.pprint p)
                                                   $+$ text ""
                                                   $+$ text "on which the subprocessor has allready been applied."
                                                   $+$ text "We reuse following proof:"
                                                   $+$ P.pprintProof proof mde

instance P.Processor proc => P.Processor (Subsumed proc) where
   data P.InstanceOf (Subsumed proc) = SSI (P.InstanceOf proc)
   type P.ProofOf (Subsumed proc)    = MaybeSubsumed (P.ProofOf proc)
   name (Subsumed proc) = P.name proc
   instanceName (SSI inst) = P.instanceName inst
   solve_ (SSI inst) prob = MaybeSubsumed Nothing `liftM` P.solve_ inst prob 
   solvePartial_ (SSI inst) rs prob = mk `liftM` P.solvePartial inst rs prob
        where mk pp = pp { P.ppResult = MaybeSubsumed Nothing $ P.ppResult pp}


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


