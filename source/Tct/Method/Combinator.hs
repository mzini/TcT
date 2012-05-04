{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ExistentialQuantification #-}

--------------------------------------------------------------------------------
-- | 
-- Module      :  Tct.Method.Combinator
-- Copyright   :  (c) Martin Avanzini <martin.avanzini@uibk.ac.at>, 
--                Georg Moser <georg.moser@uibk.ac.at>, 
--                Andreas Schnabl <andreas.schnabl@uibk.ac.at>,
-- License     :  LGPL (see COPYING)
--
-- Maintainer  :  Martin Avanzini <martin.avanzini@uibk.ac.at>
-- Stability   :  unstable
-- Portability :  unportable      
-- 
-- This module defines various processor combinators.
--------------------------------------------------------------------------------   

module Tct.Method.Combinator 
       (
         -- * Trivial Processors
         success
       , fail
       , empty
       , open
         -- ** Proof Object
       , TrivialProof (..)
       , OpenProof (..)
         -- ** Processor Definition
       , Success
       , successProcessor
       , Fail
       , failProcessor
       , EmptyRules
       , emptyProcessor
       , Open
       , openProcessor
         -- * Parallel / Sequential Proof Search
       , before
       , orFaster
       , orBetter
       , sequentially
       , fastest
       , best       
         -- ** Proof Object         
       , OneOfProof (..)
         -- ** Processor Definition         
       , OneOf (..)
       , sequentiallyProcessor
       , fastestProcessor
       , bestProcessor

         -- * Conditional
       , ite
       , IteProof (..)
       , Ite
       , iteProcessor
       
       , iteProgress
       , IteProgressProof
       , IteProgress
       )
where
import Prelude hiding (fail)
import Text.PrettyPrint.HughesPJ hiding (parens, empty)
import Control.Concurrent.PFold (pfoldA, Return (..))
import Control.Monad (forM)
import Control.Monad.Trans (liftIO)

import qualified Termlib.Trs as Trs
import Termlib.Problem (strictComponents) 
import Termlib.Utils (paragraph) 

import qualified Tct.Processor as P
import Tct.Utils.PPrint
import qualified Tct.Utils.Xml as Xml
import Tct.Utils.Enum (enumeration')
import Tct.Certificate (certified, constant)
import qualified Tct.Processor.Standard as S
import qualified Tct.Processor.Transformations as T
import Tct.Processor.Args
import qualified Tct.Processor.Args as A
import Tct.Processor.Args.Instances

-- failure and success

data TrivialProof = Succeeded 
                  | Failed
                  | Empty Bool

instance P.ComplexityProof TrivialProof where 
    answer Succeeded     = P.yesAnswer
    answer Failed        = P.NoAnswer
    answer (Empty True)  = P.CertAnswer $ certified (constant,constant)
    answer (Empty False) = P.NoAnswer
    pprintProof Succeeded     _ = text "Success"
    pprintProof Failed        _ = text "Fail"
    pprintProof (Empty True)  _ = text "Empty rules are trivially bounded"
    pprintProof (Empty False) _ = text "Empty strict component of the problem is NOT empty."
    toXml Succeeded = Xml.elt "success" [] []
    toXml Failed = Xml.elt "failed" [] []
    toXml (Empty True) = Xml.elt "empty" [] []    
    toXml (Empty False) = Xml.elt "nonempty" [] []        
-- instance P.Verifiable TrivialProof where
--     verify _ _ = P.verifyOK

data Fail = Fail deriving (Show)

instance S.Processor Fail where
    type ArgumentsOf Fail = Unit
    type ProofOf Fail     = TrivialProof
    name Fail               = "fail"
    instanceName _          = "fail"
    solve _ _               = return Failed
    description Fail        = ["Processor 'fail' always returns the answer 'No'."]
    arguments Fail          = Unit

data Success = Success deriving (Show)

instance S.Processor Success where
    type ArgumentsOf Success = Unit
    type ProofOf Success     = TrivialProof
    name Success               = "success"
    instanceName _             = "success"
    solve _ _                  = return Succeeded
    description Success        = ["Processor 'success' always returns the answer 'Yes(?,?)'."]
    arguments   Success        = Unit

data EmptyRules = EmptyRules deriving (Show)

instance S.Processor EmptyRules where
    type ArgumentsOf EmptyRules = Unit
    type ProofOf EmptyRules     = TrivialProof
    name EmptyRules               = "empty"
    solve _ prob | Trs.isEmpty $ strictComponents prob = return $ Empty True
                 | otherwise                           = return $ Empty False
    description EmptyRules       = ["Processor 'empty' returns 'Yes(O(1),O(1))' if the strict component of the problem is empty."]
    arguments   EmptyRules       = Unit

failProcessor :: S.StdProcessor Fail
failProcessor = S.StdProcessor Fail

successProcessor :: S.StdProcessor Success
successProcessor = S.StdProcessor Success

emptyProcessor :: S.StdProcessor EmptyRules
emptyProcessor = S.StdProcessor EmptyRules

-- | This processor always returns the answer @No@.
fail :: P.InstanceOf (S.StdProcessor Fail)
fail = S.StdProcessor Fail `S.withArgs` ()

-- | This processor always returns the answer @Yes(?,?)@.
success :: P.InstanceOf (S.StdProcessor Success)
success = S.StdProcessor Success `S.withArgs` ()

-- | This processor returns the answer @Yes(O(1),(1))@ if the strict component is empty.
empty :: P.InstanceOf (S.StdProcessor EmptyRules)
empty = S.StdProcessor EmptyRules `S.withArgs` ()


-- open

data OpenProof = OpenProof
instance P.ComplexityProof OpenProof
  where answer _ = P.MaybeAnswer
        pprintProof _ _ = paragraph "The problem remains open."
        
data Open = Open
instance S.Processor Open where
  type ProofOf Open = OpenProof
  type ArgumentsOf Open = A.Unit
  
  name _ = "Open"
  arguments _ = A.Unit
  solve _ _ = return OpenProof


openProcessor :: S.StdProcessor Open
openProcessor = S.StdProcessor Open

-- | This processor always returns the answer @Maybe@.
open :: P.InstanceOf (S.StdProcessor Open)
open = openProcessor `S.withArgs` ()


-- if-then-else

data Ite g t e = Ite

data IteProof g t e = IteProof { guardProof  :: P.Proof g
                               , branchProof :: Either (P.Proof t) (P.Proof e) }

instance ( P.Processor g
         , P.Processor t
         , P.Processor e           
         , P.ComplexityProof (P.ProofOf g)
         , P.ComplexityProof (P.ProofOf t)
         , P.ComplexityProof (P.ProofOf e)) => P.ComplexityProof (IteProof g t e) where
      answer p = either (P.answer . P.result) (P.answer . P.result) (branchProof p)
      
      pprintProof p mde@P.StrategyOutput = 
        paragraph ("a) We first check the conditional [" ++ (if suc then "Success" else "Fail") ++ "]:")
        $+$ (indent $ P.pprintProof (P.result $ guardProof p) mde)
        $+$ text "" 
        $+$ paragraph ("b) We continue with the " ++ (if suc then "then" else "else") ++ "-branch:")
        $+$ case branchProof p of 
               Left bp -> P.pprintProof (P.result bp) mde
               Right bp -> P.pprintProof (P.result bp) mde
          where suc = P.succeeded $ P.result $ guardProof p
                   
                  
      pprintProof p mde = 
        case branchProof p of 
          Left pb  -> P.pprintProof (P.result pb) mde
          Right pb -> P.pprintProof (P.result pb) mde

      toXml p = 
        Xml.elt "ite" [] 
          [ Xml.elt "guardProof" [] [P.toXml $ guardProof p]
          , Xml.elt "guardSuccess" [] [Xml.text $ show $ P.succeeded $ guardProof p]
          , Xml.elt "subProof" [] [sp]]
        where sp = either P.toXml P.toXml $ branchProof p
        
instance ( P.Processor g
         , P.Processor t
         , P.Processor e) 
    => S.Processor (Ite g t e) where
        type ProofOf (Ite g t e)    = IteProof g t e 
        type ArgumentsOf (Ite g t e) = Arg (Proc g) :+: Arg (Proc t) :+: Arg (Proc e)
        name Ite = "ite"
        instanceName inst = "Branch on whether processor '" ++ P.instanceName g ++ "' succeeds"
          where g :+: _ :+: _ = S.processorArgs inst
        description _ = ["This processor implements conditional branching"]
        arguments _ = arg { A.name = "guard"
                          , A.description = "The guard processor. It succeeds if it returns 'Yes(*,*)'." }
                      :+: 
                      arg { A.name = "then"
                          , A.description = "The processor that is applied if guard succeeds." }
                      :+: 
                      arg { A.name = "else"
                          , A.description = "The processor that is applied if guard fails." }
        solve inst prob = 
          do gproof <- P.apply g prob
             if P.succeeded gproof 
               then do bproof <- P.apply t prob
                       return $ IteProof { guardProof  = gproof
                                         , branchProof = Left bproof }
               else do bproof <- P.apply e prob
                       return $ IteProof { guardProof  = gproof
                                         , branchProof = Right bproof }
            where g :+: t :+: e = S.processorArgs inst

-- | @ite g t e@ applies processor @t@ if processor @g@ succeeds, otherwise processor @e@ is applied.
ite :: (P.Processor g, P.Processor t, P.Processor e) => P.InstanceOf g -> P.InstanceOf t -> P.InstanceOf e -> P.InstanceOf (S.StdProcessor (Ite g t e))
ite g t e = S.StdProcessor Ite `S.withArgs` (g :+: t :+: e)

iteProcessor :: S.StdProcessor (Ite P.AnyProcessor P.AnyProcessor P.AnyProcessor)
iteProcessor = S.StdProcessor Ite


-- branching on transformations

data IteProgress g t e = IteProgress (T.TheTransformer g)

data IteProgressProof g t e = IteProgressTransformed   (T.Proof g t) 
                            | IteProgressUntransformed (T.TheTransformer g) (T.ProofOf g) (P.Proof e)

instance ( T.Transformer g
         , P.Processor t
         , P.Processor e) => P.ComplexityProof (IteProgressProof g t e) where
  answer (IteProgressTransformed p)   = P.answer p
  answer (IteProgressUntransformed _ _ p) = P.answer p
  pprintProof (IteProgressTransformed p)   mde = P.pprintProof p mde
  pprintProof (IteProgressUntransformed tr tp p) mde = 
    case mde of 
      P.StrategyOutput ->
        paragraph "Transformation of the input failed:"
        $+$ text ""
        $+$ T.pprintTProof tr (P.inputProblem p) tp mde
        $+$ text ""        
        $+$ paragraph ("We continue with processor '" ++ P.instanceName (P.appliedProcessor p) ++ "'.")
        $+$ text ""        
        $+$ indent (P.pprintProof (P.result p) mde )
      _ -> P.pprintProof (P.result p) mde
  toXml (IteProgressTransformed p) = P.toXml p
  toXml (IteProgressUntransformed tr tp p) = 
    Xml.elt "iteProgress" []
      [ Xml.elt "failedTransformation" [] 
         [ Xml.elt n [] [T.transformerToXml tr
                        , Xml.elt "transformationProof" [] trxml]]
      , Xml.elt "subProof" [] [P.toXml p]]
    where (n,trxml) = T.tproofToXml tr (P.inputProblem p) tp

instance ( T.Transformer g
         , P.Processor t
         , P.Processor e) => S.Processor (IteProgress g t e) where
  type ProofOf (IteProgress g t e) = IteProgressProof g t e
  type ArgumentsOf (IteProgress g t e) = Arg (Proc t) :+: Arg (Proc e) :+: Arg Bool
  name _ = "iteProgress"
  arguments _ = arg { A.name = "then"
                    , A.description = "The processor that is applied if the transformation succeeds." }
                :+: 
                arg { A.name = "else"
                    , A.description = "The processor that is applied if the transformation fails." }
                :+: 
                opt { A.name = "parallel"
                    , A.description = "Decides whether the given subprocessor should be applied in parallel."
                    , A.defaultValue = False }
                

  solve inst prob = 
    do res <- T.transform g prob
       case res of 
         T.NoProgress tp -> 
           do sp <- P.apply e prob
              return $ IteProgressUntransformed g tp sp
         T.Progress _ ps -> 
           do esubproofs <- P.evalList par (P.succeeded . snd) 
                           [P.apply t prob_i >>= \ r -> return (i,r) 
                           | (i,prob_i) <- ps]
              let subproofs = case esubproofs of {Left (fld,sps) -> fld:sps; Right sps -> sps}
                  proof = T.Proof { T.transformationResult = res
                                  , T.inputProblem         = prob
                                  , T.appliedSubprocessor  = t
                                  , T.appliedTransformer   = g
                                  , T.subProofs            = subproofs}
              return $ IteProgressTransformed proof 
           
    where IteProgress g     = S.processor inst
          (t :+: e :+: par) = S.processorArgs inst
            

iteProgress :: (T.Transformer g, P.Processor t, P.Processor e) => 
              T.TheTransformer g
              -> P.InstanceOf t
              -> P.InstanceOf e
              -> P.InstanceOf (S.StdProcessor (IteProgress g t e))
iteProgress g t e = S.StdProcessor (IteProgress g) `S.withArgs` (t :+: e :+: False)


-- parallel combinators

data OneOf p = Best | Fastest | Sequentially deriving (Eq, Show)

data OneOfProof p = OneOfFailed (OneOf p) [P.Proof p]
                  | OneOfSucceeded (OneOf p) (P.Proof p)

instance (P.Processor p) => P.ComplexityProof (OneOfProof p) where
    pprintProof proof mde = 
        case proof of 
          (OneOfFailed _ failures) -> text "None of the processors succeeded."
                                     $+$ text "" 
                                     $+$ detailsFailed (enumeration' failures)
          (OneOfSucceeded o p) 
              | mde == P.StrategyOutput -> case o of 
                                           Sequentially -> paragraph (procName p ++ " succeeded:")
                                           Fastest      -> paragraph (procName p ++ " proved the goal fastest:")
                                           Best         -> paragraph (procName p ++ " proved the best result:")
                                         $+$ text ""
                                         $+$ P.pprintProof (P.result p) mde
              | otherwise              -> P.pprintProof (P.result p) mde
      where procName p = "'" ++ P.instanceName (P.appliedProcessor p) ++ "'"
            detailsFailed ps = block "Details of failed attempt(s)" 
                              $ [ (a, paragraph (procName p ++ " failed due to the following reason:")
                                      $+$ text ""
                                      $+$ (P.pprintProof (P.result p) mde))
                                | (a,p) <- ps]

    toXml (OneOfFailed p failures) = 
      Xml.elt "oneOf" []
        [ Xml.elt "combinator" [] [ Xml.text (show p) ]
        , Xml.elt "failures" [] [ P.toXml p_i | p_i <- failures ]]
    toXml (OneOfSucceeded p p_i) =       
      Xml.elt "oneOf" []
        [ Xml.elt "combinator" [] [ Xml.text (show p) ]
        , Xml.elt "subProof" [] [ P.toXml p_i ]]
    answer (OneOfFailed _ _)    = P.MaybeAnswer
    answer (OneOfSucceeded _ p) = P.answer p


instance (P.Processor p) => S.Processor (OneOf p) where
    type ArgumentsOf (OneOf p) = Arg [Proc p]
    type ProofOf (OneOf p)     = OneOfProof p

    name Fastest      = "fastest"
    name Sequentially = "sequentially"
    name Best         = "best"

    instanceName inst = c (S.processor inst) -- ++ " of " ++  (concat $ intersperse ", " [ "'" ++ P.instanceName p ++ "'" | p <- S.processorArgs inst])
        where c Best         = "Best"
              c Fastest      = "Fastest"
              c Sequentially = "Sequentially"
    description Best         = ["Processor 'Best' applies the given list of processors in parallel and returns the proof admitting the lowest complexity certificate."]
    description Fastest      = ["Processor 'Fastest' applies the given list of processors in parallel and returns the first successful proof."]
    description Sequentially = ["Processor 'Sequentially' applies the given list of processors sequentially and returns the first successful proof."]

    arguments _ = arg { A.name        = "subprocessors"
                      , A.description = "a list of subprocessors"}
    solve theproc prob | proc == Sequentially = solveSeq (S.processorArgs theproc) []
                       | proc == Best         = solveBest (S.processorArgs theproc)
                       | otherwise           = solveFast (S.processorArgs theproc)

        where proc = S.processor theproc 
              mkActions ps = forM ps $ \ p -> P.mkIO $ P.apply p prob
              ofResult o (Left faileds) = OneOfFailed o faileds
              ofResult o (Right proof) = OneOfSucceeded o proof
              
              solveSeq []     failures = return $ OneOfFailed Sequentially (reverse failures)
              solveSeq (p:ps) failures = do r <- P.apply p prob
                                            if P.succeeded r
                                             then return $ OneOfSucceeded Sequentially r
                                             else solveSeq ps (r:failures)
                                
              solveBest = solvePar betterThan final 
                  where p1 `betterThan` p2 = P.certificate p1 < P.certificate p2
                        final = const False

              solveFast= solvePar betterThan final
                  where _ `betterThan` _ = True
                        final = const True

              solvePar better final ps = do actions <- mkActions ps
                                            let sel (Left ps') proof | P.succeeded proof = ret proof
                                                                     | otherwise         = Continue $ Left (proof : ps')
                                                sel (Right p1) p2 | p1 `better` p2 = ret p1
                                                                  | otherwise      = ret p2
                                                ret proof | final proof = Stop $ Right proof
                                                          | otherwise   = Continue $ Right proof
                                            r <- liftIO $ pfoldA sel (Left []) actions
                                            return $ ofResult proc r

bestProcessor :: S.StdProcessor (OneOf P.AnyProcessor)
bestProcessor = S.StdProcessor Best

fastestProcessor :: S.StdProcessor (OneOf P.AnyProcessor)
fastestProcessor = S.StdProcessor Fastest

sequentiallyProcessor :: S.StdProcessor (OneOf P.AnyProcessor)
sequentiallyProcessor = S.StdProcessor Sequentially

-- | The processor @p1 `orFaster` p2@ applies processor @p1@ and @p2@ in parallel. Returns the 
--   proof of that processor that finishes fastest.
orFaster :: (P.Processor a, P.Processor b) => 
           P.InstanceOf a -> P.InstanceOf b -> P.InstanceOf (S.StdProcessor (OneOf P.SomeProcessor))
a `orFaster` b = fastest [P.someInstance a, P.someInstance b]

-- | The processor @p1 `orBetter` p2@ applies processor @p1@ and @p2@ in parallel. Returns the 
--   proof that gives the better certificate.
orBetter :: (P.Processor a, P.Processor b) => 
           P.InstanceOf a -> P.InstanceOf b -> P.InstanceOf (S.StdProcessor (OneOf P.SomeProcessor))
a `orBetter` b = best [P.someInstance a, P.someInstance b]

-- | The processor @p1 `before` p2@ first applies processor @p1@, and if that fails processor @p2@.
before :: (P.Processor a, P.Processor b) => 
           P.InstanceOf a -> P.InstanceOf b -> P.InstanceOf (S.StdProcessor (OneOf P.SomeProcessor))
a `before` b = sequentially [P.someInstance a, P.someInstance b]

-- | List version of 'orBetter'.
-- Note that the type of all given processors need to agree. To mix processors
-- of different type, use 'some' on the individual arguments. 
best :: (P.Processor p) => [P.InstanceOf p] -> P.InstanceOf (S.StdProcessor (OneOf p))
best ps = S.StdProcessor Best `S.withArgs` ps

-- | List version of 'orFaster'.
-- Note that the type of all given processors need to agree. To mix processors
-- of different type, use 'some' on the individual arguments. 
fastest :: (P.Processor p) => [P.InstanceOf p] -> P.InstanceOf (S.StdProcessor (OneOf p))
fastest ps = S.StdProcessor Fastest `S.withArgs` ps

-- | List version of 'before'. 
sequentially :: (P.Processor p) => [P.InstanceOf p] -> P.InstanceOf (S.StdProcessor (OneOf p))
sequentially ps = S.StdProcessor Sequentially `S.withArgs` ps
