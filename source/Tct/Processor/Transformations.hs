{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleInstances #-}
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
import qualified Tct.Processor as P
import qualified Tct.Processor.Standard as S
import Data.Maybe (fromMaybe)
import Tct.Processor.PPrint
import qualified Tct.Processor.Args as A
import Tct.Processor.Args.Instances
import Tct.Processor.Args hiding (name, description, synopsis)


--------------------------------------------------------------------------------
--- Transformation Proofs

class Verifiable proof where 
    verify :: Problem -> proof -> Enumeration (Maybe (P.Proof sub)) -> P.VerificationStatus
    verify _ _ _ = P.verifyUnchecked

-- class Answerable proof where 
--     answer :: proof -> Enumeration P.Answer -> P.Answer

-- class (PrettyPrintable (Proof t sub), Verifiable (Proof t sub), Answerable proof) => TransformationProof (ProofOf t)
-- instance (PrettyPrintable proof, Verifiable proof, Answerable proof) => TransformationProof (ProofOf t)


--------------------------------------------------------------------------------
--- Transformation Class

data Result t = Failure (ProofOf t) 
              | Success (ProofOf t) (Enumeration Problem)

data Proof t sub = Proof { transformationProof :: ProofOf t 
                         , inputProblem        :: Problem
                         , subProofs           :: Enumeration (P.Proof sub) }

data TheTransformer t = TheTransformer { transformation     :: t
                                       , isStrict           :: Bool
                                       , solveParallel      :: Bool
                                       , transformationArgs :: Domains (ArgumentsOf t)}

class TransformationProof proof where
  answer :: Problem -> proof -> Enumeration (Problem, P.InstanceOf P.SomeProcessor, P.ProofOf P.SomeProcessor) -> P.Answer
  pprint :: Problem -> proof -> Enumeration (Problem, P.InstanceOf P.SomeProcessor, P.ProofOf P.SomeProcessor) -> Doc

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


findProof :: (Numbering a) => a -> Proof t t1 -> Maybe (P.Proof t1)
findProof e p = find e (subProofs p)
findProof _ _ = Nothing

data t1 :>>>: t2 = TheTransformer t1 :>>>: TheTransformer t2
data ComposeProof t1 t2 = ComposeProof { firstproof :: ProofOf t1
                                       , sndproof   :: Maybe (Enumeration (Result t2)) }


someProofNode :: (Transformer t) => ProofOf t -> P.InstanceOf P.SomeProcessor -> Problem -> Enumeration P.SomeProof -> Proof t P.SomeProcessor
someProofNode tproof sub prob ps  = Proof { transformationProof = tproof
                                          , inputProblem        = prob
                                          , subProofs           = f `mapEnum` ps  }
  where f sp = P.Proof { P.appliedProcessor = sub
                       , P.inputProblem = prob
                       , P.result = sp}

instance (Transformer t1, Transformer t2) => TransformationProof (ComposeProof t1 t2) where
    pprint prob (ComposeProof p1 (Just ers)) subproofs  = 
      case sequence [ subproof i res_i | (i, res_i) <- ers] of 
        Nothing -> undefined
        Just sps -> pprint prob p1 (f `mapEnum` sps)
      where subproof (SN (e1 :: a)) (res :: Result t2)   = case res of
              Failure p2         -> do (subprob, subproc, subproof)  <- find (Left e1 :: Either a Int) subproofs
                                       return $ someProof $ TP (someProofNode p2 subproc subprob [(SN e1, subproof)] :: Proof t2 P.SomeProcessor) (TPUntransformed $ P.someProof subproof)
            f tp = someProofNode (P.someInstance 
--              Success p2 eprobs -> -- [ find (Right (e1,e2) :: Either Int (a,b)) subproofs 
                                  --  |  (SN (e2 :: b), _) <- eprobs ]
-- mk :: P.Processor p => P.Proof p -> (Problem, P.InstanceOf P.SomeProcessor, P.ProofOf P.SomeProcessor)
-- mk p = (P.inputProblem p, P.someInstance (P.appliedProcessor p), P.someProof (P.result p))

-- --------------------------------------------------------------------------------
-- -- SomeTransformation

-- -- data SomeTrans = forall t. (Transformer t) => SomeTrans t (Domains (ArgumentsOf t))
-- -- data SomeTransProof = forall t. SomeTransProof t

-- -- instance PrettyPrintable SomeTransProof where
-- --     pprint (SomeTransProof p) = pprint p

-- -- instance Answerable SomeTransProof where
-- --     answer (SomeTransProof p) ps = answer p ps

-- -- instance Verifiable SomeTransProof where
-- --     verify prob (SomeTransProof p) ps = verify prob p ps

-- -- instance Transformer SomeTrans where
-- --     name (SomeTrans t _) = name t
-- --     description (SomeTrans t _) = description t

-- --     type ArgumentsOf SomeTrans = Unit
-- --     type ProofOf SomeTrans     = SomeTransProof
-- --     arguments _ = Unit
-- --     transform inst@(TheTransformer (SomeTrans t as) _ _ ()) prob = 
-- --         mk `liftM` transform inst{transformation=t, transformationArgs = as} prob
-- --         where mk (Failure p) = Failure (SomeTransProof p)
-- --               mk (Success p ts) = Success (SomeTransProof p) ts

-- -- someTransformation :: (P.ComplexityProof (ProofOf t), Transformer t) => TheTransformer t -> TheTransformer SomeTrans
-- -- someTransformation inst = inst { transformation     = SomeTrans (transformation inst) (transformationArgs inst)
-- --                                , transformationArgs = ()}


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



instance (Transformer t1, Transformer t2) => Transformer (t1 :>>>: t2) where
    name (t1 :>>>: t2) = take 20 (instanceName t1) ++ " >>> " ++ take 20 (instanceName t2)
    description _ = ["Implements sequencing of two transformations"]
    type ArgumentsOf (t1 :>>>: t2) = Unit
    type ProofOf (t1 :>>>: t2)    = ComposeProof t1 t2
    arguments _ = Unit
    transform inst prob = do
      r1 <- transform t1 prob
      case r1 of 
        Failure p1       -> return $ Failure $ ComposeProof p1 Nothing
        Success p1 probs -> do r2s <- mapM transform2 probs
                               return $ Success (ComposeProof p1 (Just $ mkSubproofs r2s)) (mkSubprobs r2s)
        where t1 :>>>: t2 = transformation inst
              transform2 (e, subprob) = do r <- transform t2 subprob
                                           return (e, r, subprob)
              mkSubproofs r2s = [(e,r) | (e,r,_) <- r2s]
              mkSubprobs r2s = concatMap mkElt r2s
                  where mkElt (SN (e1 :: a), (Failure _)          , subprob) = [(SN (Left e1 :: Either a Int), subprob)]
                        mkElt (SN (e1 :: a), (Success _ esubprobs), _     )  = [(SN (Right (e1,e2) :: Either Int (a,b)), subprob) | (SN (e2 :: b), subprob) <- esubprobs ]


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


















data TPstatus t sub = TPTransformed
                    | TPFailed
                    | TPUntransformed (P.ProofOf sub)
                    | TPMissing

data TP t sub = TP (Proof t sub) (TPstatus t sub)
                
instance ( Transformer t, P.Processor sub ) => Util.PrettyPrintable (TP t sub) where 
  pprint (TP tproof status) = case status of             
    TPTransformed            -> tpdoc 
    TPUntransformed subproof -> text "Transforming the input failed. We thus apply the subprocessor directly."
                                $+$ tpdoc
                                $+$ text ""
                                $+$ block' "We apply the subprocessor directly" [subproof]
    TPFailed                 -> tpdoc
    TPMissing                -> text "Error: SUBPROOF missing!"
    where input  = inputProblem tproof
          subproofs = subProofs tproof
          tpdoc = pprint input (transformationProof tproof) (mk `mapEnum` subproofs) 
            
mk :: P.Processor p => P.Proof p -> (Problem, P.InstanceOf P.SomeProcessor, P.ProofOf P.SomeProcessor)
mk p = (P.inputProblem p, P.someInstance (P.appliedProcessor p), P.someProof (P.result p))

instance ( Transformer t, P.Processor sub ) => P.Answerable (TP t sub) where 
  answer (TP tproof status) = case status of 
    TPTransformed            -> tpanswer
    TPUntransformed subproof -> P.answer subproof
    TPFailed                 -> P.MaybeAnswer
    TPMissing                -> P.MaybeAnswer
    where input  = inputProblem tproof
          subproofs = subProofs tproof
          tpanswer = answer input (transformationProof tproof) (mk `mapEnum` subproofs)

instance P.Verifiable (TP t sub) -- MA:MISSING:
    -- verify prob p@(TProof proof subps) = verify prob proof subps `P.andVerify` 
    --                                      case subProofs p of 
    --                                        Just sps -> P.allVerify [ P.verify (P.inputProblem pp) (P.result pp) | (_, pp) <- sps ]
    --                                        Nothing  -> P.verifyFail p (text "proof of transformed problem missing")
    -- verify prob (UTProof _ sub)  = P.verify prob sub



instance ( Transformer t 
         , P.Processor sub) 
         => S.Processor (Trans t sub) where
    type S.ProofOf (Trans t sub) = TP t sub
    type S.ArgumentsOf (Trans t sub) = Arg (Maybe Bool) :+: Arg (Maybe Bool) :+: ArgumentsOf t :+: Arg (Proc sub)
    name (Trans t)      = name t
    description (Trans t) = description t
    arguments (Trans t) = opt { A.name = "strict"
                              , A.description = unlines [ "If this flag is set and the transformation fails, this processor aborts."
                                                        , "Otherwise, it applies the subprocessor on the untransformed input."] 
                              , A.defaultValue = Nothing }
                          :+: opt { A.name = "parallel"
                                  , A.description = "Decides whether the given subprocessor should be applied in parallel"
                                  , A.defaultValue = Nothing }
                          :+: arguments t 
                          :+: arg { A.name = "subprocessor"
                                  , A.description = "The processor that is applied on the transformed problem(s)" }
    solve inst prob = do res <- transform (TheTransformer t False False args) prob
                         case res of 
                           Failure p | toBool str -> return $ mkProof p  [] TPFailed
                                     | otherwise  -> (mkProof p [] . TPUntransformed) `liftM` P.solve sub prob 
                           Success p ps -> do esubproofs <- P.evalList (toBool par) (P.succeeded . snd) 
                                                            [P.apply sub p' >>= \ r -> return (e,r) | (e,p') <- ps]
                                              return $ case mkSubproofs esubproofs ps of 
                                                          Just sps -> mkProof p sps TPTransformed
                                                          Nothing  -> mkProof p [] TPMissing 

        where (Trans t) = S.processor inst
              str :+: par :+: args :+: sub = S.processorArgs inst
              toBool = maybe False id 
              mkSubproofs (Right subproofs) ps = sequence [(,) (SN e) `liftM` find e subproofs | (SN e,_) <- ps]
              mkSubproofs (Left  (fld,ss))  _  = Just (fld : ss) 
              mkProof p subproofs status = TP Proof {transformationProof = p
                                                      , inputProblem        = prob
                                                      , subProofs           = subproofs}
                                              status


data Trans t sub = Trans t
type TransformationProcessor t sub = S.StdProcessor (Trans t sub)

transformationProcessor :: (Arguments (ArgumentsOf t), ParsableArguments (ArgumentsOf t), Transformer t) => t -> TransformationProcessor t sub
transformationProcessor t = S.StdProcessor (Trans t)

withArgs :: (Transformer t) => t -> (Domains (ArgumentsOf t)) -> TheTransformer t
t `withArgs` as = TheTransformer { transformation     = t
                                 , isStrict           = False
                                 , solveParallel      = False
                                 , transformationArgs = as}

strict :: (Transformer t, S.Processor (Trans t p)) => P.InstanceOf (TransformationProcessor t p) -> P.InstanceOf (TransformationProcessor t p)
strict = S.modifyArguments $ \ (_ :+: par :+: as :+: sub) -> Just True :+: par :+: as :+: sub

nonstrict :: (Transformer t, S.Processor (Trans t p)) => P.InstanceOf (TransformationProcessor t p) -> P.InstanceOf (TransformationProcessor t p)
nonstrict = S.modifyArguments $ \ (_ :+: par :+: as :+: sub) -> Just False :+: par :+: as :+: sub

sequentialSubgoals :: (Transformer t, S.Processor (Trans t p)) => P.InstanceOf (TransformationProcessor t p) -> P.InstanceOf (TransformationProcessor t p)
sequentialSubgoals = S.modifyArguments $ \ (str :+: _ :+: as :+: sub) -> str :+: Just False :+: as :+: sub

parallelSubgoals :: (Transformer t, S.Processor (Trans t p)) => P.InstanceOf (TransformationProcessor t p) -> P.InstanceOf (TransformationProcessor t p)
parallelSubgoals = S.modifyArguments $ \ (str :+: _ :+: as :+: sub) -> str :+: Just True :+: as :+: sub


