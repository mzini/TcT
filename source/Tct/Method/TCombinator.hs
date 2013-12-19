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
       -- * Timeout
       timeout
       , Timeout (..)        
       , TimeoutProof(..)
       -- * Timed 
       , timed
       , Timed
       , TimedProof (..)
       -- * Try  
       , try
       , force         
       , Try (..)
       , TryProof (..)
       -- * Composition
       , (>>>)
       , exhaustively
       , (:>>>:)(..)
       , ComposeProof(..)
       -- , mkComposeProof
       -- * Choice
       , (<>)
       , (<||>)
       , (:<>:)(..)
       , ChoiceProof (..)
       -- * WithProblem 
       , withProblem
       , WithProblem (..)
       , WithProblemProof (..)
         
       -- * ID
       , idtrans
       , Unique (..) --TODO hide
       )
where

import Tct.Processor.Transformations

import Control.Monad (liftM)
import qualified System.Timeout as TO
import System.CPUTime (getCPUTime)
import Control.Monad.Trans (liftIO)
import Data.Time.Clock (getCurrentTime, diffUTCTime)
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
-- import qualified Tct.Processor.Standard as S
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
      [] -> Xml.elt "idtrans" [] [Xml.text "no sub-problem generated"]
      [(_,p)] -> P.toXml p
      _   -> error "proof of Id-trans contains more than one subproof"
    
  
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


instance (TransformationProof t1, Transformer t1, Transformer t2) => TransformationProof (t1 :>>>: t2) where
    answer = error "TransformationProof.answer intentionally not implemented"

    pprintTProof (TheTransformer (t1 :>>>: _) _)  prob (ComposeProof r1 Nothing) mde = 
        pprintTProof t1  prob (proofFromResult r1) mde
    pprintTProof (TheTransformer (t1 :>>>: t2) _) prob (ComposeProof r1 (Just r2s)) mde =
        case r1 of 
          Progress tproof _ -> 
            pprintTProof t1 prob tproof mde
            $+$ text ""
            $+$ ppOverviews False
          NoProgress _
            | subProgress -> ppOverviews False
            | otherwise   -> PP.empty
          
      where subProgress = any (isProgressResult . snd) r2s
            subprobs = case r1 of { Progress _ ps -> ps; _ -> enumeration' [prob] }
            ppOverviews showFailed =
              case catMaybes [ ppOverview i prob_i | (i, prob_i) <- subprobs] of 
                [(_,pp)] -> pp
                pps  -> vcat $ punctuate (text "") [ indent pp | (_,pp) <- pps]
              where 
                ppOverview sn@(SN i) prob_i = 
                  case find i r2s of 
                    Nothing   -> 
                      Just (sn, Util.paragraph "We abort on this problem. THIS SHOULD NOT HAPPEN!")
                    Just r2_i@(Progress _ _) -> 
                      Just (sn, ppRes prob_i r2_i)
                    Just r2_i@(NoProgress _) 
                      | showFailed -> Just (sn, ppRes prob_i r2_i)
                      | otherwise  -> Nothing
                                     
                ppRes prob_i r2_i =  
                  Util.paragraph ("We consider the (sub)-problem:")
                  $+$ text ""
                  $+$ Util.pprint prob_i
                  $+$ text ""
                  $+$ 
                  pprintTProof t2 prob_i (proofFromResult r2_i) mde

    normalisedProof proof = 
      case proofFromResult res of 
        ComposeProof r1 Nothing -> -- unsafePerformIO $ do
         -- hPutStr stderr ("normalise 1:" ++ name (transformation t1) ++ "\n") >> hFlush stderr 
         -- return $ 
         normalisedProof $ 
          Proof { transformationResult = r1
                , inputProblem         = input
                , appliedTransformer   = t1
                , appliedSubprocessor  = sub
                , subProofs            = subproofs }
        ComposeProof r1 (Just r2s) -> 
         -- unsafePerformIO $ do
         -- hPutStr stderr ("normalise 2:" ++ name (transformation t1) ++ "\n") >> hFlush stderr
         -- return $ 
         normalisedProof $ 
          Proof { transformationResult = r1
                , inputProblem         = input
                , appliedTransformer   = t1
                , appliedSubprocessor  = P.someInstance $ t2 `thenApply` sub
                , subProofs            = mkSubProof_i `map` r2s }
           where
             input_i (SN i) = 
               case r1 of 
                 NoProgress _        -> input
                 Progress _ subprobs -> fromMaybe (error "compose.normalisedProof problem not found") (find i subprobs)             

             -- errProofNotFound :: Numbering a => a -> b
             -- errProofNotFound num = 
             --     error $ show $ 
             --     text ">>>.normalisedProof: subproof"
             --     <+> ppNumbering num <+> text "not found in" 
             --     <+> vcat [ ppNumbering n | (SN n,_) <- subproofs ]

             subproofs_i (SN i) (NoProgress _) = 
                case r1 of 
                  NoProgress {} 
                    | length subproofs > 1 -> error ">>>.normalisedProof: at most one sub-proof expected"
                    | otherwise -> subproofs
                  Progress {} -> 
                    case find (One i) subproofs of 
                      Just pr -> [(SN i,pr)]
                      Nothing -> []
                      -- Nothing -> errProofNotFound (One i)
             subproofs_i (SN i) (Progress _ subprobs_i) = concatMap mkSubProof_j subprobs_i
               where
                 mkSubProof_j (SN j, _) = 
                   case find (Two (i,j)) subproofs of 
                     Just sp -> [(SN j, sp)]
                     Nothing -> []
                     -- Nothing    -> errProofNotFound (Two (i,j))

             mkSubProof_i (sn_i,r2_i) = 
               ( sn_i
               , P.Proof { P.appliedProcessor = P.someInstance $ appliedTransformer tproof_i `thenApply` appliedSubprocessor tproof_i
                         , P.inputProblem = input_i sn_i
                         , P.result = P.SomeProof $ tproof_i } )
               where tproof_i = normalisedProof $ 
                                Proof { transformationResult = r2_i
                                      , inputProblem         = input_i sn_i
                                      , appliedTransformer   = t2
                                      , appliedSubprocessor  = sub
                                      , subProofs            = subproofs_i sn_i r2_i }
      where 
        (TheTransformer (t1 :>>>: t2) _) = appliedTransformer proof
        sub = appliedSubprocessor proof
        input = inputProblem proof
        res = transformationResult proof
        subproofs = subProofs proof


                  
data Unique a = One a
              | Two a deriving (Typeable, Eq)

instance Numbering a => Numbering (Unique a) where 
    ppNumbering (One a) = ppNumbering a
    ppNumbering (Two a) = ppNumbering a
    -- ppNumbering (One a) = text "One(" PP.<> ppNumbering a PP.<> text ")"
    -- ppNumbering (Two a) = text "Two(" PP.<> ppNumbering a PP.<> text ")"

instance (Transformer t1, Transformer t2) => Transformer (t1 :>>>: t2) where
    name (TheTransformer t1 _ :>>>: TheTransformer t2 _ ) = take 100 $ "(" ++ name t1 ++ " >>> " ++ name t2 ++ ")"
    instanceName (TheTransformer (t1 :>>>: _) _) = instanceName t1
    description (TheTransformer t1 _ :>>>: _) = description t1
    type ArgumentsOf (t1 :>>>: t2) = Unit
    type ProofOf (t1 :>>>: t2)    = ComposeProof t1 t2
    arguments _ = Unit
    continue (TheTransformer (t1 :>>>: t2) _) = continue t1 && continue t2
    transform inst prob = do
      r1 <- transform t1 prob
      case r1 of 
        NoProgress _ 
            | continue t1 -> transform2 r1 (enumeration' [prob])
            | otherwise -> return $ NoProgress $ ComposeProof r1 Nothing
        Progress _ ps -> transform2 r1 ps

        where 
          transform2 :: P.SolverM m => Result t1 -> Enumeration Problem -> m (Result (t1 :>>>: t2))
          transform2 r1 ps = do 
             r2s <- mapM trans ps
             let tproof = ComposeProof r1 $ Just [(e1,r2_i) | (e1, r2_i,_) <- r2s]
                 esubprobs = concatMap mkSubProbs r2s
                 progressed 
                     | continue t2 = isProgressResult r1 || any isProgressResult [r2_i | (_,r2_i,_) <- r2s]
                     | otherwise   = all isProgressResult [r2_i | (_,r2_i,_) <- r2s]
                 proof 
                     | progressed = Progress tproof esubprobs
                     | otherwise  = NoProgress tproof
             return proof
              where 
                trans (e1, prob_i) = do 
                   r2_i <- transform t2 prob_i
                   return (e1, r2_i, prob_i)

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
    
  normalisedProof proof = 
    case transformationProof proof of 
      ChoiceOne r1 -> normalisedProof $ proof { transformationResult = r1 
                                             , appliedTransformer   = t1}
      ChoiceTwo r2 -> normalisedProof $ proof { transformationResult = r2
                                             , appliedTransformer   = t2}
      ChoiceSeq _ r2 -> normalisedProof $ proof { transformationResult = r2
                                               , appliedTransformer   = t2}
    where (TheTransformer t _) = appliedTransformer proof
          t1 = fstChoice t
          t2 = sndChoice t
      
  -- proofToXml proof = --TODO normalised proof?
  --   case transformationProof proof of 
  --     ChoiceOne r1 -> proofToXml $ proof { transformationResult = r1 
  --                                       , appliedTransformer   = t1}
  --     ChoiceTwo r2 -> proofToXml $ proof { transformationResult = r2
  --                                       , appliedTransformer   = t2}
  --     ChoiceSeq _ r2 -> proofToXml $ proof { transformationResult = r2
  --                                         , appliedTransformer   = t2}
  --   where (TheTransformer t _) = appliedTransformer proof
  --         t1 = fstChoice t
  --         t2 = sndChoice t



instance (Transformer t1, Transformer t2) => Transformer (t1 :<>: t2) where
  name t  = name $ transformation $ fstChoice t
  instanceName (TheTransformer t _) = instanceName $ fstChoice t
  
  type ArgumentsOf (t1 :<>: t2) = Unit
  type ProofOf (t1 :<>: t2) = ChoiceProof t1 t2
  arguments _ = Unit
  
  transform tinst prob =
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

data Try t = Try Bool t
data TryProof t = TryProof Bool (ProofOf t)

fromTry :: TheTransformer (Try t) -> TheTransformer t
fromTry (TheTransformer (Try _ t) as) = TheTransformer t as


instance (Transformer t, TransformationProof t) => TransformationProof (Try t) where
    pprintProof proof mde = 
        case result of 
          NoProgress (TryProof True p) 
              | mde == P.StrategyOutput -> 
                  pprintTProof t' (inputProblem proof) p mde
                  $+$ text ""
                  $+$ Util.paragraph "We abort the transformation and continue with the subprocessor on the previous problem" 
                  $+$ text ""
                  $+$ Util.pprint (inputProblem proof)
                  $+$ text ""
                  $+$ ppsub
              | otherwise -> ppsub
          NoProgress (TryProof False _) -> ppsub
            
          Progress {} -> P.pprintProof proof mde
      where t'        = fromTry $ appliedTransformer proof
            ppsub = case subProofs proof of 
                          []        -> text "No further proof was generated, we abort!"
                          [(_,sp)] -> P.pprintProof (P.result sp) mde
                          l        -> text "Multiple proofs were generated" 
                                      $+$ vcat [ P.pprintProof (P.result sp) mde | (_,sp) <- l ]
            result    = transformationResult proof
    answer proof = 
        case transformationResult proof of 
          Progress (TryProof _ p) ps -> 
            answer $ proof { appliedTransformer  = fromTry t
                           , transformationResult = Progress p ps}
          NoProgress (TryProof _ _)  -> 
            answerFromSubProof proof
      where t = appliedTransformer proof

    pprintTProof t prob (TryProof _ p) = pprintTProof (fromTry t) prob p

    proofToXml = proofToXml . normalisedProof
    
    normalisedProof proof = normalisedProof $ 
                     proof { appliedTransformer  = fromTry $ appliedTransformer proof
                           , transformationResult = const tproof `mapResult` transformationResult proof }
      where (TryProof _ tproof) = transformationProof proof


instance (Transformer t) => Transformer (Try t) where
    name (Try _ t) = name t
    continue inst = cont
      where Try cont _ = transformation inst
    instanceName inst = instanceName (fromTry inst)
    description (Try _ t) = description t
    type ArgumentsOf  (Try t) = ArgumentsOf t
    type ProofOf (Try t) = TryProof t
    arguments (Try _ t) = arguments t
    transform inst prob = mk `liftM` transform tinst prob
        where mk (Progress p ps) = Progress (TryProof cont p) ps
              mk (NoProgress p)  = NoProgress (TryProof cont p)
              Try cont t = transformation inst
              tinst = TheTransformer { transformation = t
                                     , transformationArgs = transformationArgs inst }

-- | The transformer @try t@ behaves like @t@ but succeeds even if @t@ fails. When @t@ fails
-- the input problem is returned.
try :: Transformer t => TheTransformer t -> TheTransformer (Try t)
try (TheTransformer t args) = TheTransformer (Try True t) args

-- | The transformer @force t@ behaves like @t@ but fails always whenever no 
-- progress is achieved.
force :: Transformer t => TheTransformer t -> TheTransformer (Try t)
force (TheTransformer t args) = TheTransformer (Try False t) args


--------------------------------------------------------------------------------
-- Timed 

data Timed t = Timed t

data TimedProof t = 
  TimedProof { tpCpu :: Double 
             , tpWall :: Double
             , tpProof :: (ProofOf t) }

fromTimed :: TheTransformer (Timed t) -> TheTransformer t
fromTimed inst = TheTransformer { transformation = t
                                , transformationArgs = transformationArgs inst }
  where Timed t = transformation inst
        
fromTimedProof :: Proof (Timed t) sub -> Proof t sub
fromTimedProof proof = 
  case transformationResult proof of 
    Progress p ps -> 
      proof { appliedTransformer   = tinst
            , transformationResult = Progress (tpProof p) ps}
    NoProgress p  -> 
      proof { appliedTransformer   = tinst
            , transformationResult = NoProgress $ tpProof p}
  where tinst = fromTimed $ appliedTransformer proof



instance (Transformer t, TransformationProof t) => TransformationProof (Timed t) where
    pprintProof proof mde = 
      P.pprintProof (fromTimedProof proof) mde 
      $+$ text ""
      $+$ ( text "Wall-time:" <+> text (show (tpWall p)) PP.<> text "s"
            $+$ text "CPU-time:" <+> text (show (tpCpu p)) PP.<> text "s")

      where p = transformationProof proof
    answer = P.answer . fromTimedProof

    pprintTProof t prob p mde = 
      pprintTProof (fromTimed t) prob (tpProof p) mde
      $+$ text ""
      $+$ ( text "Wall-time:" <+> text (show (tpWall p)) PP.<> text "s"
            $+$ text "CPU-time:" <+> text (show (tpCpu p)) PP.<> text "s")

    -- proofToXml = proofToXml . normalisedProof . fromTimedProof

    normalisedProof = normalisedProof . fromTimedProof

instance (Transformer t) => Transformer (Timed t) where
    name (Timed t) = name t
    
    continue = continue . fromTimed
    
    instanceName = instanceName . fromTimed
    
    description (Timed t) = description t
    
    type ArgumentsOf  (Timed t) = ArgumentsOf t
    
    type ProofOf (Timed t) = TimedProof t
    
    arguments (Timed t) = arguments t
    
    transform inst prob = do 
      startCpuTime <- liftIO $ getCPUTime
      startWallTime <- liftIO $ getCurrentTime 
      res <- transform (fromTimed inst) prob
      endCpuTime <- liftIO $ getCPUTime 
      endWallTime <- liftIO $ getCurrentTime        
      let cputime = fromInteger (endCpuTime - startCpuTime) / fromInteger ((10 :: Integer)^(12 :: Integer))
          walltime = fromRational $ toRational $ diffUTCTime endWallTime startWallTime
      return $ mapResult (\ p -> TimedProof { tpCpu = cputime, tpWall = walltime, tpProof = p}) res

-- | The transformer @timed t@ behaves like @t@ but additionally measures the execution time.
timed :: Transformer t => TheTransformer t -> TheTransformer (Timed t)
timed (TheTransformer t args) = TheTransformer (Timed t) args

--------------------------------------------------------------------------------
-- Timeout Transformation

data Timeout t = Timeout t Int
data TimeoutProof t = NoTimeout (ProofOf t)
                    | TimedOut Int

fromTimeout :: TheTransformer (Timeout t) -> TheTransformer t
fromTimeout (TheTransformer (Timeout t _) as) = TheTransformer t as

instance (Transformer t, TransformationProof t) => TransformationProof (Timeout t) where
    answer proof = 
      case transformationProof proof of 
        TimedOut _ -> P.MaybeAnswer
        _          -> P.answer proof
    pprintTProof tinst prob (NoTimeout p) mde = pprintTProof (fromTimeout tinst) prob p mde
    pprintTProof _ _ (TimedOut i) _ = 
      paragraph ("Computation stopped due to timeout after " 
                 ++ show (double (fromIntegral i)) ++ " seconds.")
    normalisedProof proof = 
      case transformationProof proof of 
        NoTimeout p -> 
          normalisedProof $ 
          proof { appliedTransformer = fromTimeout $ appliedTransformer proof
                , transformationResult = mapResult (const p) $ transformationResult proof }
        _ -> someProof proof
instance (Transformer t) => Transformer (Timeout t) where
    name (Timeout t _) = name t
    description (Timeout t _) = description t
    type ArgumentsOf (Timeout t) = ArgumentsOf t
    type ProofOf (Timeout t) = TimeoutProof t
    arguments (Timeout t _) = arguments t
    transform inst prob = 
      do io <- P.mkIO $ transform tinst prob
         r <- liftIO $ TO.timeout (i * (10^(6 :: Int))) io
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

instance (Transformer t) => TransformationProof (WithProblem t) where
    answer = P.answer
    pprintProof = P.pprintProof
    pprintTProof _ prob (WithProblemProof tinst proof) = pprintTProof tinst prob proof
    -- proofToXml = proofToXml . normalisedProof
    normalisedProof proof = normalisedProof $ 
      proof { appliedTransformer = tinst
            , transformationResult = mapResult (const tproof) $ transformationResult proof }
      where WithProblemProof tinst tproof = transformationProof proof
            
withProblem :: (Problem -> TheTransformer t) -> TheTransformer (WithProblem t)
withProblem f = TheTransformer (WithProblem f)  ()