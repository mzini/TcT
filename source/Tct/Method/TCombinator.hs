{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ScopedTypeVariables #-}
--------------------------------------------------------------------------------
-- | 
-- Module      :  Tct.Method.TCombinator
-- Copyright   :  (c) Martin Avanzini <martin.avanzini@uibk.ac.at>, 
--                Georg Moser <georg.moser@uibk.ac.at>, 
--                Andreas Schnabl <andreas.schnabl@uibk.ac.at>,
-- License     :  LGPL (see COPYING)
--
-- Maintainer  :  Martin Avanzini <martin.avanzini@uibk.ac.at>
-- Stability   :  unstable
-- Portability :  unportable      
-- 
-- This module implements all transformation combinators.
--------------------------------------------------------------------------------   

module Tct.Method.TCombinator (
       timeout
       , Timeout         
       , try
       , Try
       , (>>>)
       , (<>)
       , (<||>)
       , exhaustively
       , idtrans
       , WithProblem
       , withProblem
       ) 
where

import Tct.Processor.Transformations

import Control.Monad (liftM)

import Control.Concurrent.Utils (timedKill)
import Control.Monad.Trans (liftIO)

import Data.Maybe (catMaybes)
import Text.PrettyPrint.HughesPJ hiding (empty, (<>))
import qualified Text.PrettyPrint.HughesPJ as PP
import Data.Typeable
import Data.Maybe (fromMaybe)

import Termlib.Problem
import qualified Termlib.Utils as Util
import Termlib.Utils (paragraph)

import Tct.Utils.Enum
import qualified Tct.Utils.Xml as Xml
import Tct.Utils.PPrint
import qualified Tct.Processor as P
import qualified Tct.Processor.Standard as S
import qualified Tct.Processor.Args as A
import Tct.Processor.Args hiding (name, description, synopsis)

--------------------------------------------------------------------------------
-- Id
              
data Id = Id

data IdProof = IdProof

instance TransformationProof Id where
  pprintTProof _ _ _ _ = PP.empty
  answer = answerFromSubProof
  proofToXml proof = 
    case subProofs proof of 
      [(_,p)] -> P.toXml p
      _   -> error "proof of Id-trans does not contain subproof"
    
  
instance Transformer Id where 
  name Id = "id"
  description Id = []
  type ArgumentsOf Id = Unit
  type ProofOf Id     = IdProof
  arguments Id = Unit
  transform _ _ = return $ NoProgress IdProof

-- | Identity transformation.
idtrans :: TheTransformer Id
idtrans = Transformation Id `withArgs` ()

--------------------------------------------------------------------------------
--- Composition

data t1 :>>>: t2 = TheTransformer t1 :>>>: TheTransformer t2
data ComposeProof t1 t2 = ComposeProof (Result t1) (Maybe (Enumeration (Result t2)))


instance (Transformer t1, Transformer t2) => TransformationProof (t1 :>>>: t2) where
    pprintProof proof mde =
      case tproof of 
         ComposeProof r1 Nothing    -> pprintTProof t1 input (proofFromResult r1) mde
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

    pprintTProof (TheTransformer (t1 :>>>: _) _)  prob (ComposeProof r1 Nothing) mde = 
        pprintTProof t1  prob (proofFromResult r1) mde
    pprintTProof (TheTransformer (t1 :>>>: t2) _) prob (ComposeProof r1 (Just r2s)) mde =
        case r1 of 
          Progress tproof _ -> 
            pprintTProof t1 prob tproof mde
            $+$ text ""
            $+$ ppOverviews False
          NoProgress tproof 
            | subProgress -> ppOverviews False
            | otherwise   -> pprintTProof t1 prob tproof mde
                            $+$ ppOverviews True
          
      where subProgresseds = [ r | r@(_, Progress _ _) <- r2s ]
            subProgress = not (null subProgresseds)
            subprobs = case r1 of { Progress _ ps -> ps; _ -> enumeration' [prob] }
            ppOverviews showFailed =
              case subprobs of 
                [(i,prob_i)] -> ppOverview i prob_i
                _            -> vcat [ block' (show $ text "Sub-problem" <+> Util.pprint i) [ppOverview i prob_i] 
                                    | (i, prob_i) <- subprobs]
              where ppOverview (SN i) prob_i = 
                      case find i r2s of 
                        Nothing   -> Util.paragraph "We abort on this problem. THIS SHOULD NOT HAPPEN!"
                        Just r2_i@(Progress _ _) -> 
                          ppRes prob_i r2_i
                        Just r2_i@(NoProgress _) 
                          | showFailed   -> ppRes prob_i r2_i   
                          | otherwise -> PP.empty
                    ppRes prob_i r2_i =  
                      Util.paragraph ("We apply the transformation '" ++ instanceName t2 ++ "' on the sub-problem:")
                      $+$ text ""
                      $+$ Util.pprint prob_i
                      $+$ text ""
                      $+$ pprintTProof t2 prob_i (proofFromResult r2_i) mde

    proofToXml proof = 
      case tproof of 
         ComposeProof r1 Nothing -> 
           proofToXml $ Proof { transformationResult = r1
                              , inputProblem = input
                              , appliedSubprocessor = sub
                              , appliedTransformer = t1
                              , subProofs = subproofs }
         ComposeProof r1 (Just r2s) -> 
           proofToXml (mkComposeProof sub t1 t2 input r1 r2s subproofs)
      where tproof    = transformationProof proof
            input     = inputProblem proof
            subproofs = P.someProcessorProof `mapEnum` subProofs proof
            sub       = P.someInstance (appliedSubprocessor proof)
            TheTransformer (t1 :>>>: t2) () = appliedTransformer proof
            

-- % maybe should return Try t1 proof
mkComposeProof :: (P.Processor sub, Transformer t1, Transformer t2) => P.InstanceOf sub -> TheTransformer t1 -> TheTransformer t2 -> Problem -> Result t1 -> [(SomeNumbering, Result t2)] -> Enumeration (P.Proof sub) -> Proof t1 (S.StdProcessor (Transformation (Try t2) sub))
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
                                                                   , appliedSubprocessor  = mkSubsumed sub
                                                                   , subProofs            = enumeration' $ catMaybes [liftMS Nothing `liftM` find (One i) subproofs] } 

                                  Progress p2_i subprobs_i -> Proof { transformationResult = Progress (TryProof p2_i) subprobs_i
                                                                   , inputProblem         = prob_i
                                                                   , appliedTransformer   = t2try
                                                                   , appliedSubprocessor  = mkSubsumed sub
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
    instanceName (TheTransformer (t1 :>>>: _) _) = instanceName t1
    description (TheTransformer t1 _ :>>>: _) = description t1
    type ArgumentsOf (t1 :>>>: t2) = Unit
    type ProofOf (t1 :>>>: t2)    = ComposeProof t1 t2
    arguments _ = Unit
    continue (TheTransformer (t1 :>>>: t2) _) = continue t1 && continue t2
    transform inst prob = do
      r1 <- transform t1 prob
      case r1 of 
        NoProgress _   -> if continue t1
                         then transform2 r1 (enumeration' [prob])
                         else return $ NoProgress $ ComposeProof r1 Nothing
        Progress _ ps -> transform2 r1 ps -- [(a,prob1), (b,prob2), (c,prob3)...]

        where transform2 :: P.SolverM m => Result t1 -> Enumeration Problem -> m (Result (t1 :>>>: t2))
              transform2 r1 ps = do r2s <- mapM trans ps
                                    let tproof = ComposeProof r1 $ Just [(e1,r2_i) | (e1, r2_i,_) <- r2s]
                                        esubprobs = concatMap mkSubProbs r2s
                                        progressed | continue t2 = isProgressResult r1 || any isProgressResult [r2_i | (_,r2_i,_) <- r2s]
                                                   | otherwise   = all isProgressResult [r2_i | (_,r2_i,_) <- r2s]
                                        proof | progressed = Progress tproof esubprobs
                                              | otherwise  = NoProgress tproof
                                    return $ proof
                  where trans (e1, prob_i) = do {r2_i <- transform t2 prob_i; return (e1, r2_i, prob_i)}

                        mkSubProbs (SN e1, Progress _ subprobs, _     ) = [(SN (Two (e1,e2)), subprob) | (SN e2, subprob) <- subprobs]
                        mkSubProbs (SN e1, NoProgress _       , prob_i) = [(SN (One e1), prob_i)]

              t1 :>>>: t2 = transformation inst

-- | The transformer @t1 >>> t2@ first transforms using @t1@, resulting subproblems are 
-- transformed using @t2@. 
infixr 6 >>>
(>>>) :: (Transformer t1, Transformer t2) => TheTransformer t1 -> TheTransformer t2 -> TheTransformer SomeTransformation
t1 >>> t2 = someTransformation inst 
    where inst = TheTransformer (t1 :>>>: t2) ()


-- | The transformer @exhaustively t@ applies @t@ repeatedly until @t@ fails.
-- @exhaustively t == t '>>>' try (exhaustively t)@.
exhaustively :: Transformer t => TheTransformer t -> TheTransformer SomeTransformation
exhaustively t = t >>> try (exhaustively t)


--------------------------------------------------------------------------------
-- Choice
              
data t1 :<>: t2 = Choice { fstChoice :: TheTransformer t1  
                         , sndChoice :: TheTransformer t2
                         , parChoice :: Bool }

data ChoiceProof t1 t2 = ChoiceOne (Result t1)
                       | ChoiceTwo (Result t2)
                       | ChoiceSeq (Result t1) (Result t2) 
                       
instance (Transformer t1, Transformer t2) => TransformationProof (t1 :<>: t2) where
  pprintTProof (TheTransformer t _) prob (ChoiceOne r1) mde = 
    pprintTProof (fstChoice t) prob (proofFromResult r1) mde
  pprintTProof (TheTransformer t _) prob (ChoiceTwo r2) mde = 
    pprintTProof (sndChoice t) prob (proofFromResult r2) mde
  pprintTProof (TheTransformer t _) prob (ChoiceSeq r1 r2) P.StrategyOutput = 
    Util.paragraph ("We fail transforming the problem using '" ++ instanceName t1 ++ "':")
    $+$ text ""
    $+$ indent (pprintTProof t1 prob (proofFromResult r1) P.StrategyOutput)
    $+$ text ""
    $+$ Util.paragraph ("We try instead '" ++ instanceName t2 ++ "'. We reconsider following problem:")
    $+$ text ""    
    $+$ Util.pprint prob
    $+$ text ""
    $+$ indent (pprintTProof t2 prob (proofFromResult r2) P.StrategyOutput)
      where t1 = fstChoice t
            t2 = sndChoice t
            
  pprintTProof (TheTransformer t _) prob (ChoiceSeq _ r2) mde =     
    pprintTProof (sndChoice t) prob (proofFromResult r2) mde
    
  answer proof = 
    case transformationProof proof of 
      ChoiceOne r1 -> answer $ proof { transformationResult = r1 
                                    , appliedTransformer   = t1}
      ChoiceTwo r2 -> answer $ proof { transformationResult = r2
                                    , appliedTransformer   = t2}
      ChoiceSeq _ r2 -> answer $ proof { transformationResult = r2
                                      , appliedTransformer   = t2}
    where (TheTransformer t _) = appliedTransformer proof
          t1 = fstChoice t
          t2 = sndChoice t
    
  proofToXml proof = 
    case transformationProof proof of 
      ChoiceOne r1 -> proofToXml $ proof { transformationResult = r1 
                                        , appliedTransformer   = t1}
      ChoiceTwo r2 -> proofToXml $ proof { transformationResult = r2
                                        , appliedTransformer   = t2}
      ChoiceSeq _ r2 -> proofToXml $ proof { transformationResult = r2
                                          , appliedTransformer   = t2}
    where (TheTransformer t _) = appliedTransformer proof
          t1 = fstChoice t
          t2 = sndChoice t



instance (Transformer t1, Transformer t2) => Transformer (t1 :<>: t2) where
  name t  = name $ transformation $ fstChoice t
  instanceName (TheTransformer t _) = instanceName $ fstChoice t
  
  type ArgumentsOf (t1 :<>: t2) = Unit
  type ProofOf (t1 :<>: t2) = ChoiceProof t1 t2
  arguments _ = Unit
  
  transform tinst prob =
    -- | not (parChoice t) = 
    -- do r1 <- transform t1 prob
    --    case r1 of 
    --      Progress _ ps -> return $ Progress (ChoiceOne r1) ps
    --      NoProgress _  -> 
    --        do r2 <- transform t2 prob
    --           return $ case r2 of 
    --                     Progress _ ps -> Progress (ChoiceSeq r1 r2) ps
    --                     NoProgress _  -> NoProgress (ChoiceSeq r1 r2)
     -- | otherwise = 
         do rs <- P.evalList (parChoice t) (not . isProgress) [ Left `liftM` transform t1 prob
                                                  , Right `liftM` transform t2 prob]
            let toResult :: Either (Result t1) (Result t2) -> Result (t1 :<>: t2)
                toResult (Left  r1@(Progress _ ps)) = Progress (ChoiceOne r1) ps 
                toResult (Left  r1@(NoProgress _))  = NoProgress (ChoiceOne r1)
                toResult (Right r2@(Progress _ ps)) = Progress (ChoiceTwo r2) ps 
                toResult (Right r2@(NoProgress _))  = NoProgress (ChoiceTwo r2)

                select r@Progress{}                _                           = r
                select _                           r@Progress{}                = r
                select (NoProgress (ChoiceOne r1)) (NoProgress (ChoiceTwo r2)) = NoProgress (ChoiceSeq r1 r2)
                select (NoProgress (ChoiceTwo r2)) (NoProgress (ChoiceOne r1)) = NoProgress (ChoiceSeq r1 r2)
                select _                           _                           = error "Transformation.choice.select: impossible arguments given"

            return $ case rs of 
              Left (r, _) -> toResult r
              Right [r] -> toResult r
              Right [r1, r2] -> select (toResult r1) (toResult r2)
              Right _ -> error "Transformation.choice: insufficient or more than one result returned"
    where t = transformation tinst
          t1 = fstChoice t
          t2 = sndChoice t
          isProgress (Left (Progress {})) = True
          isProgress (Right (Progress {})) = True
          isProgress _ = False
           
-- | The transformer @t1 \<\> t2@ transforms the input using @t1@ if successfull, otherwise
-- @t2@ is applied.
infixr 8 <>
(<>) :: (Transformer t1, Transformer t2) => TheTransformer t1 -> TheTransformer t2 -> TheTransformer SomeTransformation
t1 <> t2 = someTransformation inst 
    where inst = TheTransformer t ()
          t = Choice { fstChoice = t1
                     , sndChoice = t2
                     , parChoice = False}

-- | The transformer @t1 \<||\> t2@ applies the transformations @t1@ and
-- @t2@ in parallel, using the result of whichever transformation succeeds first.
infixr 7 <||>
(<||>) :: (Transformer t1, Transformer t2) => TheTransformer t1 -> TheTransformer t2 -> TheTransformer SomeTransformation
t1 <||> t2 = someTransformation inst 
    where inst = TheTransformer t ()
          t = Choice { fstChoice = t1
                     , sndChoice = t2
                     , parChoice = True }


--------------------------------------------------------------------------------
-- Try Transformation

data Try t = Try t
data TryProof t = TryProof (ProofOf t)

fromTry :: TheTransformer (Try t) -> TheTransformer t
fromTry (TheTransformer (Try t) as) = TheTransformer t as


instance (Transformer t, TransformationProof t) => TransformationProof (Try t) where
    pprintProof proof mde = 
        case result of 
          NoProgress (TryProof p) 
              | mde == P.StrategyOutput -> 
                  pprintTProof t' (inputProblem proof) p mde
                  $+$ text ""
                  $+$ Util.paragraph "We abort the transformation and continue with the subprocessor on the previous problem" 
                  $+$ text ""
                  $+$ Util.pprint (inputProblem proof)
                  $+$ text ""
                  $+$ ppsub
              | otherwise -> ppsub
                  
          Progress (TryProof p) _ -> pprintProof proof { appliedTransformer  = t'
                                                      , transformationResult = const p `mapResult` result } mde
      where t         = appliedTransformer proof
            t'        = fromTry t
            msubproof = case subProofs proof of 
                          [(_,sp)] -> Just $ P.result sp
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

    -- tproofToXml t prob (TryProof p) = 
      
    proofToXml proof = 
      proofToXml proof { appliedTransformer  = t'
                       , transformationResult = const p `mapResult` result }
      where t'        = fromTry $ appliedTransformer proof
            result    = transformationResult proof
            p = case transformationResult proof of 
                  NoProgress (TryProof p') -> p'
                  Progress (TryProof p') _ -> p'                 



instance (Transformer t) => Transformer (Try t) where
    name (Try t) = name t
    continue _ = True
    instanceName inst = instanceName (fromTry inst)
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

-- | The transformer @try t@ behaves like @t@ but succeeds even if @t@ fails. When @t@ fails
-- the input problem is returned.
try :: Transformer t => TheTransformer t -> TheTransformer (Try t)
try (TheTransformer t args) = TheTransformer (Try t) args

--------------------------------------------------------------------------------
-- Timeout Transformation

data Timeout t = Timeout t Int
data TimeoutProof t = NoTimeout (ProofOf t)
                    | TimedOut Int

fromTimeout :: TheTransformer (Timeout t) -> TheTransformer t
fromTimeout (TheTransformer (Timeout t _) as) = TheTransformer t as

instance (Transformer t, TransformationProof t) => TransformationProof (Timeout t) where
    answer proof = 
        case transformationResult proof of 
          Progress (NoTimeout p) ps -> answer $ proof { appliedTransformer   = t
                                                     , transformationResult = Progress p ps}
          NoProgress (NoTimeout p)  -> answer $ proof { appliedTransformer   = t
                                                     , transformationResult = NoProgress p }
          _                         -> P.MaybeAnswer
          where t = fromTimeout $ appliedTransformer proof
    pprintTProof tinst prob (NoTimeout p) mde = pprintTProof (fromTimeout tinst) prob p mde
    pprintTProof _ _ (TimedOut i) _ = 
      paragraph ("Computation stopped due to timeout after " 
                 ++ show (double (fromIntegral i)) ++ " seconds.")

    -- tproofToXml t prob (TryProof p) = 
      
    proofToXml proof =  
        case transformationResult proof of 
          Progress (NoTimeout p) ps -> proofToXml $ proof { appliedTransformer   = t
                                                         , transformationResult = Progress p ps}
          NoProgress (NoTimeout p)  -> proofToXml $ proof { appliedTransformer   = t
                                                         , transformationResult = NoProgress p }
          _                         -> Xml.elt "timeout" [] [Xml.text $ show i]
          where t = fromTimeout $ appliedTransformer proof
                Timeout _ i = transformation $ appliedTransformer proof


instance (Transformer t) => Transformer (Timeout t) where
    name (Timeout t _) = name t
    description (Timeout t _) = description t
    type ArgumentsOf (Timeout t) = ArgumentsOf t
    type ProofOf (Timeout t) = TimeoutProof t
    arguments (Timeout t _) = arguments t
    transform inst prob = 
      do io <- P.mkIO $ transform tinst prob
         r <- liftIO $ timedKill (i * (10^(6 :: Int))) io
         return $ case r of 
                   Just (Progress p ps) -> Progress (NoTimeout p) ps
                   Just (NoProgress p) -> NoProgress (NoTimeout p)
                   Nothing -> NoProgress (TimedOut i)
        where Timeout t i = transformation inst 
              tinst = TheTransformer { transformation = t
                                     , transformationArgs = transformationArgs inst }

timeout :: Int -> TheTransformer t -> TheTransformer (Timeout t)
timeout i (TheTransformer t args) = TheTransformer (Timeout t i) args


----------------------------------------------------------------------
--- with problem

data WithProblem t = WithProblem (Problem -> TheTransformer t)
data WithProblemProof t = WithProblemProof (TheTransformer t) (ProofOf t)

instance (Transformer t) => Transformer (WithProblem t) where
    name _ = "With Problem ..."
    description _ = []
    type ArgumentsOf (WithProblem t) = A.Unit
    type ProofOf (WithProblem t) = WithProblemProof t
    arguments _ = A.Unit
    transform inst prob = 
      mapResult (WithProblemProof tinst) `liftM` transform tinst prob
        where WithProblem f = transformation inst 
              tinst = f prob 
              
              
liftWPProof :: (Proof t sub -> r) -> Proof (WithProblem t) sub -> r
f `liftWPProof` p = f p { appliedTransformer = tinst
                        , transformationResult = mapResult (const tproof) $ transformationResult p }
  where WithProblemProof tinst tproof = transformationProof p

instance (Transformer t) => TransformationProof (WithProblem t) where
    answer proof = answer `liftWPProof` proof
    pprintProof proof = pprintProof `liftWPProof` proof          
    pprintTProof _ prob (WithProblemProof tinst proof) = pprintTProof tinst prob proof
    proofToXml proof = proofToXml `liftWPProof` proof  


withProblem :: (Problem -> TheTransformer t) -> TheTransformer (WithProblem t)
withProblem f = TheTransformer (WithProblem f)  ()