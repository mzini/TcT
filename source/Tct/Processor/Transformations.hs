{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}

--------------------------------------------------------------------------------
-- | 
-- Module      :  Tct.Processor.Transformations
-- Copyright   :  (c) Martin Avanzini <martin.avanzini@uibk.ac.at>, 
--                Georg Moser <georg.moser@uibk.ac.at>, 
--                Andreas Schnabl <andreas.schnabl@uibk.ac.at>,
-- License     :  LGPL (see COPYING)
--
-- Maintainer  :  Martin Avanzini <martin.avanzini@uibk.ac.at>
-- Stability   :  unstable
-- Portability :  unportable      
-- 
-- This module gives the infrastructure for /transformation processors/.
-- Transformation processors transform an input problem into zero or more
-- subproblems, reflecting the complexity of the input problem.
-- Transformations abort if the input problem cannot be simplified. 
-- Use 'try' to continue with the input problem.
--------------------------------------------------------------------------------   

module Tct.Processor.Transformations 
       (
         -- * Using Transformations          
         TheTransformer (..)
         -- ** Lifting to Processors       
       , (>>|)
       , (>>||)         
         
         -- * Defining new Transformations
         -- | In order to define a new transformation, 
         -- define an instance of 'Transformer' and 'TransformationProof'. 
         -- Use 'withArgs' for providing an instance constructor, compare "Tct.instances".
         -- Use 'transformationProcessor' to lift the defined transformation to a processor.
       , Transformer (..)
       , TransformationProof (..)         
       , Transformation (..)
       , withArgs
       , modifyArguments
       , transformationProcessor
         -- ** Transformation Result
       , Result (..)
       , proofFromResult
       , subProblemsFromResult
       , isProgressResult
       , mapResult
       , sanitiseResult
         
         -- ** Transformation Proof
       , Proof (..)
       , subProblems
       , findProof
       , transformationProof
       , answerFromSubProof
                  
         -- * Existential Quantification
       , SomeTransformation (..)
       , SomeTransProof (..)
       , someTransformation
       , someProof
         
         -- * Subsumed Processor
         -- | The following utilities are used only internally.
       , liftMS
       , mkSubsumed
         
         -- * Misc
       , transformerToXml
       , thenApply
       )
where

import Control.Monad (liftM)

import Data.Maybe (catMaybes)
import Text.PrettyPrint.HughesPJ hiding (empty, (<>))
import qualified Text.PrettyPrint.HughesPJ as PP
import qualified Data.Set as Set
import Data.List (partition)

import Termlib.Problem
import qualified Termlib.Trs as Trs
import qualified Termlib.Utils as Util

import Tct.Utils.Enum
import qualified Tct.Utils.Xml as Xml
import Tct.Utils.PPrint
import qualified Tct.Processor as P
import qualified Tct.Proof as Proof
import qualified Tct.Processor.Standard as S
import qualified Tct.Processor.Args as A
import Tct.Processor.Args.Instances
import Tct.Processor.Args hiding (name, description, synopsis)

--------------------------------------------------------------------------------
--- Transformation Proofs


transformerToXml :: Transformer t => TheTransformer t -> Xml.XmlContent
transformerToXml tinst = 
  Xml.elt "transformationProcessor" [] 
    [ Xml.elt "arguments" [] $ A.toXml (arguments t) (transformationArgs tinst)
    , Xml.elt "name" [] [Xml.text $ name t]
    , Xml.elt "description" [] [Xml.text $ unwords $ description t]]
    where t = transformation tinst
          
-- | Every transformer needs to implement this class.
-- Minimal definition: 'answer' and 'pprintTProof'.
class TransformationProof t where
  
  -- | Construct an 'P.Answer' from the 'Proof'.
  answer :: P.Processor sub => Proof t sub -> P.Answer
  
  -- | Construct an Xml-node from a transformation proof.
  -- The default implementation wraps the pretty-printed output
  -- in a 'proofdata' node
  tproofToXml :: (Transformer t) => TheTransformer t -> Problem -> ProofOf t -> (String, [Proof.XmlContent])
  tproofToXml t prob proof = 
    ( name (transformation t)
    , [ Xml.elt "proofdata" [] [Xml.text $ show $ pprintTProof t prob proof P.ProofOutput] ])
    
  proofToXml :: (Transformer t, P.Processor sub) => Proof t sub -> Proof.XmlContent
  proofToXml proof = 
    Xml.elt "transformation" [] 
     [ transformerToXml tinst
     , Xml.complexityProblem input ans
     , Xml.elt "transformationProof" [] [Xml.elt n [] cnt]
     , Xml.elt (if progressed then "progress" else "noprogress") [] []
     , Xml.elt "subProofs" [] [Proof.toXml p | (_,p) <- subproofs ]]
    where (n, cnt)  = tproofToXml tinst input tproof 
          subproofs = subProofs proof
          tproof    = transformationProof proof
          tinst     = appliedTransformer proof
          input     = inputProblem proof
          ans       = answer proof
          progressed = isProgressResult $ transformationResult proof
          
  -- | Pretty print the transformation proof.
  pprintTProof :: TheTransformer t -> Problem -> ProofOf t -> P.PPMode -> Doc
  
  -- | Pretty printer of the 'Proof'. A default implementation is given.
  pprintProof :: P.Processor sub => Proof t sub -> P.PPMode -> Doc
  pprintProof proof mde = 
      ppTransformationDetails 
      $+$ case subprobs of 
            []   -> text "Transformation failed, no sub-problems were generated."
            [_]  -> ppDetails Nothing
            _    -> ppOverviews
                   $+$ text ""
                   $+$ ppDetails (Just "Proofs for generated problems")
      where subproofs = subProofs proof
            subprobs  = subProblems proof
            tproof    = transformationProof proof
            t         = appliedTransformer proof
            input     = inputProblem proof
            ppTransformationDetails 
              | mde == P.OverviewOutput = PP.empty
              | otherwise = pprintTProof t input tproof mde
                            $+$ text ""
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

-- | Result type for a transformation.
data Result t = NoProgress (ProofOf t)  -- ^ The transformation did not simplify the problem.
              | Progress (ProofOf t) (Enumeration Problem) -- ^ The transformation resulted in the given subproblems.


-- | This is the proof of a transformation lifted to a processor.  
data Proof t sub = Proof { transformationResult :: Result t -- ^ The 'Result' generated by the transformation
                         , inputProblem         :: Problem -- ^ The input problem
                         , appliedTransformer   :: TheTransformer t -- ^ The instance of the applied transformation
                         , appliedSubprocessor  :: P.InstanceOf sub -- ^ The instance of the applied subprocessor
                         , subProofs            :: Enumeration (P.Proof sub) -- ^ An enumeration of the subproofs 
                         }


-- | If the proof contains exactly one subproblem, return the 
-- computed certificate of this problem. Otherwise, return 'P.MaybeAnswer'.
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

subProblemsFromResult :: Result r -> Enumeration Problem
subProblemsFromResult (Progress _ ps) = ps
subProblemsFromResult (NoProgress _)  = []

mapResult :: (ProofOf t1 -> ProofOf t2) -> Result t1 -> Result t2
mapResult f (NoProgress p)  = NoProgress (f p)
mapResult f (Progress p ps) = Progress (f p) ps

sanitiseResult :: Result t1 -> Result t1
sanitiseResult (Progress p ps) = Progress p $ mapEnum sanitise ps
sanitiseResult res             = res

transformationProof :: Proof t sub -> ProofOf t
transformationProof tproof = case transformationResult tproof of 
                               NoProgress p -> p
                               Progress p _ -> p
                               
subProblems :: Proof t sub -> Enumeration Problem
subProblems tproof = subProblemsFromResult $ transformationResult tproof 

findProof :: (Numbering a) => a -> Proof t sub -> Maybe (P.Proof sub)
findProof e p = find e (subProofs p)

--------------------------------------------------------------------------------
--- Transformation Class

-- | This datatype defines a specific instance of a transformation.
data TheTransformer t = TheTransformer { transformation :: t -- ^ The Transformation.
                                       , transformationArgs :: Domains (ArgumentsOf t) -- ^ Arguments of the transformation.
                                       }


-- | The main class a transformation implements.
class (Arguments (ArgumentsOf t), TransformationProof t) => Transformer t where
    -- | Unique name.
    name         :: t -> String 
    -- | Description of the transformation.
    description  :: t -> [String] 
    description  = const []

    -- | Arguments of the transformation, cf. "Tct.Processor.Args".
    type ArgumentsOf t
    -- | Proof type of the transformation.    
    type ProofOf t
    
    -- | Description of the arguments, cf. module "Tct.Processor.Args".
    arguments    :: t -> (ArgumentsOf t)
    
    -- | Optional name specific to instances. Defaults to the transformation name.
    instanceName :: TheTransformer t -> String
    instanceName = name . transformation
    -- | This is the main method of a transformation. Given a concrete
    -- instance, it translates a complexity problem into a 'Result'.
    transform    :: P.SolverM m => TheTransformer t -> Problem -> m (Result t)
    
    -- | If 'True', then the processor will pretend that
    -- the input problem was simplified, independent on the result of 'transform'.
    -- This is used for implementing transformation 'Try', and should not be defined.
    continue :: TheTransformer t -> Bool
    continue _ = False

--------------------------------------------------------------------------------
-- SomeTransformation

data SomeTransformation = forall t. (Transformer t) => SomeTransformation t (Domains (ArgumentsOf t))
data SomeTransProof = forall t. (Transformer t, TransformationProof t) => SomeTransProof (TheTransformer t) (ProofOf t)

someProof :: (Transformer t, P.Processor sub) => P.InstanceOf sub -> TheTransformer t -> Problem -> Result t -> Enumeration (P.Proof sub) -> Proof t P.SomeProcessor
someProof sub t prob res subproofs = Proof { transformationResult = res
                                           , inputProblem         = prob
                                           , appliedTransformer   = t
                                           , appliedSubprocessor  = P.someInstance sub
                                           , subProofs            = (P.someProofNode sub prob . P.result) `mapEnum` subproofs }


onSomeProof :: P.Processor sub' => 
              (forall t sub. (Transformer t, P.Processor sub) => Proof t sub -> a) -> Proof SomeTransformation sub' -> a
f `onSomeProof` proof = 
  case transformationProof proof of 
    SomeTransProof tinst tproof -> 
        f proof { transformationResult = 
                     case transformationResult proof of 
                       NoProgress _  -> NoProgress tproof
                       Progress _ ps -> Progress tproof ps
                , appliedTransformer = tinst }
                
instance TransformationProof SomeTransformation where
  answer proof = answer `onSomeProof` proof 
  pprintProof proof = pprintProof `onSomeProof` proof
  pprintTProof _ prob (SomeTransProof t p) = pprintTProof t prob p
  proofToXml proof = proofToXml `onSomeProof` proof
  tproofToXml _ prob (SomeTransProof t p) = tproofToXml t prob p
  
  
  

instance Transformer SomeTransformation where
    name (SomeTransformation t _) = name t
    continue (TheTransformer (SomeTransformation t as)  _) = continue (TheTransformer t as)
    
    instanceName (TheTransformer (SomeTransformation t as)  _) = instanceName (TheTransformer t as)
    description (SomeTransformation t _) = description t

    type ArgumentsOf SomeTransformation= Unit
    type ProofOf SomeTransformation    = SomeTransProof
    arguments _ = Unit
    transform inst@(TheTransformer (SomeTransformation t as) ()) prob = 
        mk `liftM` transform inst{transformation=t, transformationArgs = as} prob
        where mk (NoProgress p) = NoProgress (SomeTransProof tinst p)
              mk (Progress p ts) = Progress (SomeTransProof tinst p) ts
              tinst = TheTransformer t as



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
        

-- | Provides a lifting from 'Transformer' to 'S.Processor'.
data Transformation t sub = Transformation t

instance ( Transformer t , P.Processor sub) => S.Processor (Transformation t sub) where
    type ProofOf (Transformation t sub)     = Proof t (Subsumed sub)
    type ArgumentsOf (Transformation t sub) = Arg Bool :+: Arg Bool :+: Arg Bool :+: ArgumentsOf t :+: Arg (Proc sub)
    
    name (Transformation t)        = name t
    instanceName inst              = instanceName tinst
        where _ :+: _ :+: _ :+: as :+: _ = S.processorArgs inst
              Transformation t           = S.processor inst
              tinst                      = TheTransformer t as
    description (Transformation t) = description t
    arguments (Transformation t)   = opt { A.name = "strict"
                                         , A.description = unlines [ "If this flag is set and the transformation fails, this processor aborts."
                                                                   , "Otherwise, it applies the subprocessor on the untransformed input."] 
                                         , A.defaultValue = False }
                                     :+: 
                                     opt { A.name = "parallel"
                                         , A.description = "Decides whether the given subprocessor should be applied in parallel."
                                         , A.defaultValue = False }
                                     :+: 
                                     opt { A.name = "checkSubsumed"
                                         , A.description = unlines [ "This flag determines whether the processor should reuse proofs in case that one generated problem subsumes another one."
                                                                   , "A problem (A) is subsumed by problem (B) if the complexity of (A) is bounded from above by the complexity of (B)."
                                                                   , "Currently we only take subset-inclusions of the different components into account." ]
                                                    
                                         , A.defaultValue = False }
                                     :+: 
                                     arguments t 
                                     :+: 
                                     arg { A.name = "subprocessor"
                                         , A.description = "The processor that is applied on the transformed problem(s)" }
    solve inst prob = do res <- sanitiseResult `liftM` transform tinst prob
                         case res of 
                           NoProgress _  -> 
                             if continue tinst || not str
                             then do sp <- P.apply sub prob
                                     return $ mkProof res (enumeration' [liftMS Nothing sp])
                             else return $ mkProof res []
                           Progress _ ps -> 
                             do let (subsumed, unsubsumed) | checkSubsume = splitSubsumed ps
                                                           | otherwise    = ([], ps)
                                esubproofs <- P.evalList par (P.succeeded . snd) 
                                             [P.apply sub p' >>= \ r -> return (e,r) | (e,p') <- unsubsumed]
                                let subproofs = case esubproofs of { Left (fld,sps) -> fld:sps; Right sps -> sps }
                                    unsubsumedProofs = mapEnum (liftMS Nothing) subproofs
                                    subsumedProofs = catMaybes [ do proof_i <- find e_i subproofs
                                                                    return $ (SN e_j, liftMS (Just p_i) proof_i)
                                                               | (SN e_i, p_i, SN e_j) <- subsumed ]
                                return $ mkProof res $ unsubsumedProofs ++ subsumedProofs
                                          
        where (Transformation t) = S.processor inst
              tinst         = TheTransformer t args
              str :+: par :+: checkSubsume :+: args :+: sub = S.processorArgs inst
              splitSubsumed [] = ([],[])
              splitSubsumed ((e_i, p_i):ps) = ([ (e_i, p_i, e_j) | (e_j, _) <- subs_i ] ++ subs', unsubs')
                where (subs_i, unsubs_i) = partition (\ (_, p_j) -> p_i `subsumes` p_j) ps
                      (subs', unsubs') = splitSubsumed unsubs_i
              mkProof res subproofs = Proof { transformationResult = res
                                            , inputProblem         = prob
                                            , appliedSubprocessor  = (SSI sub)
                                            , appliedTransformer   = tinst
                                            , subProofs            = subproofs}


instance ( Transformer t, P.Processor sub ) => P.ComplexityProof (Proof t sub) where 
  pprintProof proof mde 
     | continue (appliedTransformer proof) 
       && not (isProgressResult (transformationResult proof)) = 
           case subProofs proof of 
              [(_, subproof)] -> P.pprintProof (P.result subproof) mde
              _               -> text "No subproof generated, we abort!"
     | otherwise = pprintProof proof mde
  answer proof
     | continue (appliedTransformer proof) 
       && not (isProgressResult (transformationResult proof)) = 
           answerFromSubProof proof
     | otherwise = answer proof

  toXml proof = proofToXml proof
  

-- | Constructor for instances.
withArgs :: (Transformer t) => (Transformation t sub) -> (Domains (ArgumentsOf t)) -> TheTransformer t
(Transformation t) `withArgs` as = TheTransformer t as 

-- | Modify parameters of instance
modifyArguments :: (Transformer t) => (Domains (ArgumentsOf t) -> Domains (ArgumentsOf t)) -> (TheTransformer t -> TheTransformer t)
modifyArguments f (TheTransformer t as) = TheTransformer t (f as)

-- | Lifts transformations to standard processors.
transformationProcessor :: (Arguments (ArgumentsOf t), ParsableArguments (ArgumentsOf t), Transformer t) => t -> S.StdProcessor (Transformation t sub)
transformationProcessor t = S.StdProcessor (Transformation t)


-------------------------------------------------------------------------------- 
--- utility functions for constructing and modifying transformations

someTransformation :: Transformer t => TheTransformer t -> TheTransformer SomeTransformation
someTransformation inst = inst { transformation     = SomeTransformation (transformation inst) (transformationArgs inst)
                               , transformationArgs = ()}


type TransformationInstance t sub = P.InstanceOf (S.StdProcessor (Transformation t sub))

infixr 2 `thenApply`
thenApply :: (P.Processor sub, Transformer t) => TheTransformer t -> P.InstanceOf sub -> TransformationInstance t sub
thenApply ti@(TheTransformer t args) sub = (S.StdProcessor $ Transformation t) `S.withArgs` (not (continue ti) :+: False :+: False :+: args :+: sub)

infixr 2 >>|
-- | The processor @t '>>|' p@ first applies the transformation @t@. If this succeeds, the processor @p@
-- is applied on the resulting subproblems. Otherwise @t '>>|' p@ fails.
(>>|) :: (P.Processor sub, Transformer t) => TheTransformer t -> P.InstanceOf sub -> TransformationInstance t sub
(>>|) = thenApply


infixr 2 `thenApplyPar`
thenApplyPar :: (P.Processor sub, Transformer t) => TheTransformer t -> P.InstanceOf sub -> TransformationInstance t sub
thenApplyPar ti@(TheTransformer t args) sub = (S.StdProcessor $ Transformation t) `S.withArgs` (not (continue ti) :+: True :+: False :+: args :+: sub)


infixr 2 >>||
-- | Like '>>|' but resulting subproblems are solved in parallel by the given processor.
(>>||) :: (P.Processor sub, Transformer t) => TheTransformer t -> P.InstanceOf sub -> TransformationInstance t sub
(>>||) = thenApplyPar

-- parallelSubgoals :: (P.Processor sub, Transformer t) => TransformationInstance t sub -> TransformationInstance t sub
-- parallelSubgoals = S.modifyArguments $ \ (str :+: _ :+: subs :+: as :+: sub) -> str :+: True :+: subs :+: as :+: sub

--- utility functions for constructing and modifying transformations

-- checkSubsumed :: (P.Processor sub, Transformer t) => TransformationInstance t sub -> TransformationInstance t sub
-- checkSubsumed = S.modifyArguments $ \ (str :+: par :+: _ :+: as :+: sub) -> str :+: par :+: True :+: as :+: sub


-------------------------------------------------------------------------------- 
--- subsumed processor
data Subsumed sub = Subsumed sub

data MaybeSubsumed proof = MaybeSubsumed (Maybe Problem) proof

liftMS :: Maybe Problem -> P.Proof proc -> P.Proof (Subsumed proc)
liftMS mprob proof = proof { P.appliedProcessor = SSI (P.appliedProcessor proof)
                           , P.result           = MaybeSubsumed mprob (P.result proof) }

instance P.ComplexityProof proof => P.ComplexityProof (MaybeSubsumed proof) where 
  answer (MaybeSubsumed _ proof) = P.answer proof
  pprintProof (MaybeSubsumed Nothing  proof) mde = P.pprintProof proof mde
  pprintProof (MaybeSubsumed (Just p) proof) mde = Util.paragraph "The complexity of the input problem is bounded by the complexity of the problem"
                                                   $+$ text ""
                                                   $+$ indent (Util.pprint p)
                                                   $+$ text ""
                                                   $+$ Util.paragraph "on which the subprocessor has allready been applied. We reuse following proof:"
                                                   $+$ text ""
                                                   $+$ P.pprintProof proof mde
  toXml (MaybeSubsumed Nothing proof) = P.toXml proof
  toXml (MaybeSubsumed _       proof) = P.toXml proof  

instance P.Processor proc => P.Processor (Subsumed proc) where
   data InstanceOf (Subsumed proc) = SSI (P.InstanceOf proc)
   type ProofOf (Subsumed proc)    = MaybeSubsumed (P.ProofOf proc)
   name (Subsumed proc) = P.name proc
   instanceName (SSI inst) = P.instanceName inst
   processorToXml (SSI inst) = P.processorToXml inst
   solve_ (SSI inst) prob = MaybeSubsumed Nothing `liftM` P.solve_ inst prob 
   solvePartial_ (SSI inst) rs prob = mk `liftM` P.solvePartial inst rs prob
        where mk pp = pp { P.ppResult = MaybeSubsumed Nothing $ P.ppResult pp}

mkSubsumed :: P.InstanceOf proc -> P.InstanceOf (Subsumed proc)
mkSubsumed = SSI