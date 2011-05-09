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

class TransformationProof proof where
  answer :: Problem -> proof -> Enumeration P.SomeProof -> P.Answer
  pprint :: Problem -> proof -> Enumeration P.SomeProof -> Doc
  pprint = error "define in terms of pprintProof"
  pprintProof :: Problem -> proof -> Doc
  continue :: proof -> Bool
  continue = const False

data Result t = NoProgress (ProofOf t)
              | Progress (ProofOf t) (Enumeration Problem)


data Proof t sub = Proof { transformationResult :: Result t
                         , inputProblem         :: Problem
                         , subProofs            :: Enumeration (P.ProofOf sub) }

proofFromResult :: Result t -> (ProofOf t)
proofFromResult (NoProgress t) = t
proofFromResult (Progress t _) = t

transformationProof :: Proof t sub -> ProofOf t
transformationProof tproof = case transformationResult tproof of 
                               NoProgress p -> p
                               Progress p _ -> p
                               
subProblems :: Proof t sub -> Enumeration Problem
subProblems tproof = case transformationResult tproof of 
                       Progress _ ps -> ps
                       NoProgress _  -> []

findProof :: (Numbering a) => a -> Proof t sub -> Maybe (P.ProofOf sub)
findProof e p = find e (subProofs p)
findProof _ _ = Nothing

someProof :: (Transformer t) => Problem -> Result t -> Enumeration P.SomeProof -> Proof t P.SomeProcessor
someProof prob res subproofs = Proof { transformationResult = res
                                     , inputProblem         = prob
                                     , subProofs            = subproofs }

--------------------------------------------------------------------------------
--- Transformation Class


data TheTransformer t = TheTransformer { transformation :: t
                                       , transformationArgs :: Domains (ArgumentsOf t)}

class TransformationProof (ProofOf t) => Transformer t where
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
    solve inst prob = do res <- transform (TheTransformer t args) prob
                         case res of 
                           NoProgress _  -> return $ mkProof res []
                           Progress _ ps -> do esubproofs <- P.evalList (toBool par) (P.succeeded . snd) 
                                                           [P.solve sub p' >>= \ r -> return (e,r) | (e,p') <- ps]
                                               return $ case mkSubproofs esubproofs ps of 
                                                           Just sps -> mkProof res sps
                                                           Nothing  -> mkProof res []
        where (TransProc t) = S.processor inst
              str :+: par :+: args :+: sub = S.processorArgs inst
              toBool = maybe False id 
              mkSubproofs (Right subproofs) ps = sequence [(,) (SN e) `liftM` find e subproofs | (SN e,_) <- ps]
              mkSubproofs (Left  (fld,ss))  _  = Just (fld : ss)
              mkProof res subproofs = Proof { transformationResult = res
                                            , inputProblem         = prob
                                            , subProofs            = subproofs}


instance P.Verifiable (Proof t sub)

instance ( Transformer t, P.Processor sub ) => Util.PrettyPrintable (Proof t sub) where 
  pprint proof = pprint input tproof (P.SomeProof `mapEnum` subproofs) 
    where input  = inputProblem proof
          subproofs = subProofs proof
          tproof = transformationProof proof

instance ( Transformer t, P.Processor sub ) => P.Answerable (Proof t sub) where 
  answer proof = answer input tproof (P.SomeProof `mapEnum` subproofs)
    where input  = inputProblem proof
          subproofs = subProofs proof
          tproof    = transformationProof proof

--------------------------------------------------------------------------------
--- Transformation Combinators

data t1 :>>>: t2 = TheTransformer t1 :>>>: TheTransformer t2
data ComposeProof t1 t2 = ComposeProof { firstproof :: Result t1
                                       , sndproof   :: Maybe (Enumeration (Result t2)) }



(>>>) :: (Transformer t1, Transformer t2) => TheTransformer t1 -> TheTransformer t2 -> TheTransformer SomeTrans
t1 >>> t2 = someTransformation inst 
    where inst = TheTransformer (t1 :>>>: t2) ()

exhaustively :: Transformer t => TheTransformer t -> TheTransformer SomeTrans
exhaustively t = t >>> try (exhaustively t)

data Custom res = Custom { as :: String 
                         , code :: forall m. (P.SolverM m) => Problem -> m (res, Maybe [Problem]) }

instance Transformer (Custom res) where
    name = as
    description c = [as c]
    
    type ArgumentsOf (Custom res) = Unit
    type ProofOf (Custom res) = res
    transform (TheTransformer (Custom _ code) _) prob = do (res, mprobs) <- code prob
                                                           case mprobs of 
                                                             Just probs -> Progress res (enumeration' prob)
                                                             Nothing    -> NoProgress res

custom :: String -> (forall m. (P.SolverM m) => Problem -> m res) -> TheTransformer (Custom res)
custom n m = TheTransformer (Custom n m) ()

 

instance (Transformer t1, Transformer t2) => TransformationProof (ComposeProof t1 t2) where

    pprint prob (ComposeProof r1 Nothing)    _ = pprintProof prob (proofFromResult r1)
    pprint prob (ComposeProof r1 (Just r2s)) subproofs = Util.pprint $ mkComposeProof prob r1 r2s subproofs

    answer _    (ComposeProof _ Nothing)     _ = P.MaybeAnswer
    answer prob (ComposeProof r1 (Just r2s)) subproofs = P.answer $ mkComposeProof prob r1 r2s subproofs

    pprintProof prob (ComposeProof r1 Nothing)    = pprintProof prob (proofFromResult r1)
    pprintProof prob (ComposeProof r1 (Just r2s)) = block' "Details first transformation" [pprintProof prob (proofFromResult r1)]
                                                    $+$ ppsubs
        where ppsubs = case r1 of 
                       NoProgress {} -> text ""
                       Progress _ p2s -> block "Details second transformation" [ (e1,pp e1 prob_i) | (e1,prob_i) <- p2s]
                           where pp (SN e1) prob_i = text "transformation of the following problem"
                                                     $+$ Util.pprint prob_i 
                                                     $+$ block' "Details" [fromMaybe (text "TRANSFORMATIONPROOF is missing") ppr2i]
                                     where ppr2i = do r2i <- find e1 r2s
                                                      return $ pprintProof prob_i (proofFromResult r2i)

mkComposeProof :: (Transformer t1, Transformer t2) => Problem -> Result t1 -> [(SomeNumbering, Result t2)] -> Enumeration P.SomeProof -> Proof t1 P.SomeProcessor

mkComposeProof prob r1 r2s subproofs = case r1 of 
                                         NoProgress _  -> someProof prob r1 subproofs
                                         Progress _ _ ->  someProof prob r1 subproofs1
    where subproofs1 = concatMap mkSubProof1 r2s
          mkSubProof1 (SN i, NoProgress _) = case find (One i) subproofs of 
                                                Just proof -> [(SN i, P.SomeProof proof)]
                                                Nothing    -> []
          mkSubProof1 (SN i, r2@(Progress _ subprobs)) = [(SN i, P.SomeProof $ someProof prob r2 subproofs2)]
              where subproofs2 = concatMap mkSubProof2 subprobs
                    mkSubProof2 (SN j, _) = case find (Two (i,j)) subproofs of 
                                              Just proof -> [(SN j, P.SomeProof proof)]
                                              Nothing    -> []

                  
-- pprint prob (proofFromResult r1) subproofs'
--       where subproofs' = undefined -- [ subproof e1 |  (e1, _) <- r2s]
--             subproof :: (Numbering e1) => e1 -> Maybe (Proof t2 P.SomeProcessor)
--             subproof (e1 :: e1) = 
--                 case r1 of
--                   NoProgress p2   -> do p2i <- find (One e1) subproofs
--                                         return $ someProof prob r1 [(SN e1,P.SomeProof p2i)]
--                   Progress p2 p2s -> undefined


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
        NoProgress p1  -> if continue p1 
                         then transform2 r1 (enumeration' [prob]) 
                         else return $ NoProgress $ ComposeProof r1 Nothing
        Progress _ ps -> transform2 r1 ps 

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

instance TransformationProof (ProofOf t) => TransformationProof (TryProof t) where
    continue = const True
    pprint prob (TryProof False p) [(_,subproof)] = text "Transformation failed:"
                                                    $+$ nest 1 (pprintProof prob p) 
                                                    $+$ text "We continue with the subprocessor"
                                                    $+$ Util.pprint subproof
    pprint prob (TryProof True p) subproofs = pprint prob p subproofs 

    answer _    (TryProof False _) [(_,subproof)] = P.answer subproof
    answer prob (TryProof True p)  subproofs = answer prob p subproofs
    pprintProof prob (TryProof _ p) = pprintProof prob p

instance (Transformer t) => Transformer (Try t) where
    name (Try t) = "trying " ++ name t
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
data SomeTransProof = forall t. (TransformationProof t) => SomeTransProof t

instance TransformationProof SomeTransProof where
    answer prob (SomeTransProof p) subproofs = answer prob p subproofs
    pprint prob (SomeTransProof p) subproofs = pprint prob p subproofs
    pprintProof prob (SomeTransProof p) = pprintProof prob p
    continue (SomeTransProof p) = continue p

-- instance PrettyPrintable SomeTransProof where
--     pprint (SomeTransProof p) = pprint p

-- instance Answerable SomeTransProof where
--     answer (SomeTransProof p) ps = answer p ps

-- instance Verifiable SomeTransProof where
--     verify prob (SomeTransProof p) ps = verify prob p ps

instance Transformer SomeTrans where
    name (SomeTrans t _) = name t
    description (SomeTrans t _) = description t

    type ArgumentsOf SomeTrans = Unit
    type ProofOf SomeTrans     = SomeTransProof
    arguments _ = Unit
    transform inst@(TheTransformer (SomeTrans t as) ()) prob = 
        mk `liftM` transform inst{transformation=t, transformationArgs = as} prob
        where mk (NoProgress p) = NoProgress (SomeTransProof p)
              mk (Progress p ts) = Progress (SomeTransProof p) ts

someTransformation :: (Transformer t) => TheTransformer t -> TheTransformer SomeTrans
someTransformation inst = inst { transformation     = SomeTrans (transformation inst) (transformationArgs inst)
                               , transformationArgs = ()}


-- --------------------------------------------------------------------------------
-- --- Transformation Composition

-- -- (>>>) :: (Transformer t1, Transformer t2) => TheTransformer t1 -> TheTransformer t2 -> TheTransformer (t1 :>>>: t2) 
-- -- t1 >>> t2 = TheTransformer { transformation = t1 :>>>: t2
-- --                            , isStrict       = False
-- --                            , solveParallel  = False
-- --                            , transformationArgs = ()}

--     --   (ComposeProof p1 mers) = transformationProof tproof
--     --   (ComposeProof p1 Nothing)    = pprint p1
--     -- pprint (ComposeProof p1 (Just ers)) = 
--     --     pprint p1
--     --     $+$ block "Further processing of following problems:"
--     --             [ (e,pp p eprobs) | (e, Success p eprobs) <- ers] where
--     --                 pp p eprobs = pprint p
--     --                               $+$ block "resulting in:" [(e, pprint prob) | (e,prob) <- eprobs]



-- -- data Proof t sub = Proof { transformationProof :: (ProofOf t) 
-- --                          , inputProblem        :: Problem
-- --                          , subProofs           :: (Enumeration (P.Proof sub)) }

-- instance (P.Answerable (ProofOf t1), P.Answerable (ProofOf t2)) => P.Answerable (Proof (t1 :>>>: t2) sub) where
  -- answer tproof = fromMaybe P.MaybeAnswer $ 
  --   do ers <- mers 
  --      rpp <- zipSafe mers (subProofs tproof)
  --      undefined
  --     where ComposeProof p1 mers = transformationProof tproof
  --           answer2 n1@(SN (e1 :: a)) res = (,) n1 `liftM` mans 
  --             where mans = case res of 
  --                    Failure _         -> find (Left e1 :: Either a Int) undefined
  --                    Success p2 eprobs -> undefined-- answer p2 `liftM` sequence [ find (Right (e1,e2) :: Either Int (a,b)) undefined | (SN (e2 :: b),_) <- eprobs]  





-- -- strict (A >>> B) = (nonstrict A >>> strict B)
-- -- nonstrict (A >>> B) = (nonstrict A >>> nonstrict B)
-- -- par (A >>> B) = (par A >>> B)
-- -- seq (A >>> B) = (seq A >>> B)

-- data t1 :<?>: t2 = TheTransformer t1 :<?>: TheTransformer t2

-- (<?>) :: TheTransformer t1 -> TheTransformer t2 -> TheTransformer (t1 :<?>: t2)
-- t1 <?> t2 = TheTransformer { transformation = t1 :<?>: t2
--                            , isStrict       = False
--                            , solveParallel  = False
--                            , transformationArgs = ()}

-- instance (Transformer t1, Transformer t2) => Transformer ( t1 :<?>: t2) where
--     name (t1 :<?>: t2) = take 20 (instanceName t1) ++ " <?> " ++ take 20 (instanceName t2)
--     description _ = ["Implements choice on two transformations"]
--     type ArgumentsOf (t1 :<?>: t2) = Unit
--     type ProofOf ( t1 :<?>: t2)    = ComposeProof t1 t2
--     arguments _ = Unit
--     transform inst prob = do
--       r1 <- transform t1 prob
--       case r1 of 
--         Failure p1       -> undefined
--         Success p1 probs -> undefined
--       return undefined  
--         where t1 :<?>: t2 = transformation inst

-- data Ident = Ident 
-- data IdentProof = IdentProof
-- ident = TheTransformer { transformation = Ident
--                        , isStrict       = False
--                        , solveParallel  = False
--                        , transformationArgs = ()}

-- instance Transformer Ident where
--     transform _ prob = undefined
--     type (ArgumentsOf Ident) = Unit
--     type (ProofOf Ident) = IdentProof





type TransformationProcessor t sub = S.StdProcessor (TransProc t sub)

-- transformationProcessor :: (Arguments (ArgumentsOf t), ParsableArguments (ArgumentsOf t), Transformer t) => t -> TransformationProcessor t sub
-- transformationProcessor t = S.StdProcessor (Trans t)

calledWith :: (Transformer t) => t -> (Domains (ArgumentsOf t)) -> TheTransformer t
t `calledWith` as = TheTransformer t as 


thenApply :: (P.Processor sub, Transformer t) => TheTransformer t -> P.InstanceOf sub -> P.InstanceOf (S.StdProcessor (TransProc t sub))
thenApply (TheTransformer t args) sub = (S.StdProcessor $ TransProc t) `S.withArgs` (Nothing :+: Nothing :+: args :+: sub)


-- strict :: (Transformer t, S.Processor (Trans t p)) => P.InstanceOf (TransformationProcessor t p) -> P.InstanceOf (TransformationProcessor t p)
-- strict = S.modifyArguments $ \ (_ :+: par :+: as :+: sub) -> True :+: par :+: as :+: sub

-- nonstrict :: (Transformer t, S.Processor (Trans t p)) => P.InstanceOf (TransformationProcessor t p) -> P.InstanceOf (TransformationProcessor t p)
-- nonstrict = S.modifyArguments $ \ (_ :+: par :+: as :+: sub) -> False :+: par :+: as :+: sub

-- sequentialSubgoals :: (Transformer t, S.Processor (Trans t p)) => P.InstanceOf (TransformationProcessor t p) -> P.InstanceOf (TransformationProcessor t p)
-- sequentialSubgoals = S.modifyArguments $ \ (str :+: _ :+: as :+: sub) -> str :+: False :+: as :+: sub

-- parallelSubgoals :: (Transformer t, S.Processor (Trans t p)) => P.InstanceOf (TransformationProcessor t p) -> P.InstanceOf (TransformationProcessor t p)
-- parallelSubgoals = S.modifyArguments $ \ (str :+: _ :+: as :+: sub) -> str :+: True :+: as :+: sub


class Verifiable proof where 
    verify :: Problem -> proof -> Enumeration (Maybe (P.Proof sub)) -> P.VerificationStatus
    verify _ _ _ = P.verifyUnchecked

-- instance ( Verifiable proof
--          , P.Answerable (TProof t sub)
--          , PrettyPrintable (TProof t sub)
--          , P.Verifiable (P.ProofOf sub)
--          , ProofOf t ~ proof)  => P.Verifiable (TProof t sub) where
--     verify prob p@(TProof proof subps) = verify prob proof subps `P.andVerify` 
--                                          case subProofs p of 
--                                            Just sps -> P.allVerify [ P.verify (P.inputProblem pp) (P.result pp) | (_, pp) <- sps ]
--                                            Nothing  -> P.verifyFail p (text "proof of transformed problem missing")
--     verify prob (UTProof _ sub)  = P.verify prob sub
