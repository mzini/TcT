{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DeriveDataTypeable #-}

--------------------------------------------------------------------------------
-- | 
-- Module      :  Tct.Method.ComposeRC
-- Copyright   :  (c) Martin Avanzini <martin.avanzini@uibk.ac.at>, 
--                Georg Moser <georg.moser@uibk.ac.at>, 
--                Andreas Schnabl <andreas.schnabl@uibk.ac.at>,
-- License     :  LGPL (see COPYING)
--
-- Maintainer  :  Martin Avanzini <martin.avanzini@uibk.ac.at>
-- Stability   :  unstable
-- Portability :  unportable      
-- 
-- This module provides the /compose-RC/ transformation.
--------------------------------------------------------------------------------   

module Tct.Method.ComposeRC 
       (
         composeRC
       , solveAWith
       , solveBWith         
       , composeRCselect
         -- * Proof Object
       , ComposeRCProof (..)
         -- * Processor
       , composeRCProcessor
       , ComposeRC
       )
where

import Control.Monad (liftM, mplus)
import Text.PrettyPrint.HughesPJ
import qualified Data.Set as Set
import qualified Data.List as List
import Data.Maybe (catMaybes)

import qualified Tct.Processor as P
import qualified Tct.Processor.Transformations as T
import qualified Tct.Processor.Args as A
import Tct.Utils.Enum
import Tct.Utils.PPrint
import Tct.Processor.Args
import Tct.Processor.Args.Instances
import qualified Tct.Certificate as Cert

import Termlib.Trs.PrettyPrint (pprintNamedTrs)
import Termlib.Utils (PrettyPrintable (..), snub)
import qualified Termlib.Term as Term
import qualified Termlib.Trs as Trs
import qualified Termlib.Signature as Sig
import qualified Termlib.Variable as V
import Termlib.Rule (Rule(..))
import qualified Termlib.FunctionSymbol as F
import qualified Termlib.Problem as Prob
import Tct.Method.DP.DependencyGraph
import qualified Tct.Method.DP.DependencyGraph as DG
import Tct.Method.RuleSelector
import Data.Graph.Inductive.Query.DFS (dfs)
import qualified Data.Graph.Inductive.Graph as Gr
import Data.Graph.Inductive.Query.TransClos (trc)
import Data.Typeable ()
import Data.Either (partitionEithers)

data ComposeRC p1 p2 = ComposeRC
data ComposeRCProof p1 p2 = ComposeRCProof { cpRuleSelector :: RuleSelector ()
                                           , cpUnselected   :: Trs.Trs
                                           , cpSelected     :: Trs.Trs 
                                           , cpCut          :: Trs.Trs 
                                           , cpUncut        :: Trs.Trs 
                                           , cpUnchanged    :: Trs.Trs
                                           , cpProofA       :: Maybe (P.Proof p1) 
                                           , cpProofB       :: Maybe (P.Proof p2)
                                           , cpProbA        :: Prob.Problem
                                           , cpProbB        :: Prob.Problem
                                           , cpWdg          :: DG.DG
                                           , cpSig          :: F.Signature
                                           , cpVars         :: V.Variables }
                          | ComposeRCInapplicable String

progress :: (P.Processor p1, P.Processor p2) => ComposeRCProof p1 p2 -> Bool
progress ComposeRCInapplicable {} = False
progress proof = maybe True P.succeeded (cpProofA proof) 
                 && maybe True P.succeeded (cpProofB proof)
                 && not (Trs.isEmpty (cpCut proof)) 
                 && not (Trs.isEmpty (cpUncut proof))

instance AssocArgument (RuleSelector ()) where 
    assoc _ = [] -- TODO extend


instance (P.Processor p1, P.Processor p2) => T.Transformer (ComposeRC p1 p2) where
    type T.ArgumentsOf (ComposeRC p1 p2) = Arg (Assoc (RuleSelector ())) :+: Arg (Maybe (Proc p1)) :+: Arg (Maybe (Proc p2))
    type T.ProofOf (ComposeRC p1 p2)     = ComposeRCProof p1 p2

    name _ = "compose-rc"
    instanceName inst = show $ text "compose-rc" <+> parens (ppsplit)
        where split :+: _ = T.transformationArgs inst
              ppsplit = text $ show split 

    description _ = 
      [ unwords 
        [ "This processor implements processor 'compose' specifically for the" 
        , "(weak) dependency pair setting."
        , "It tries to estimate the complexity of the input problem"
        , "based on the complexity of dependency pairs of upper congruence classes"
        , "(with respect to the congruence graph)"
        , "relative to the dependency pairs in the remaining lower congruence classes."
        , "The overall upper bound for the complexity of the input problem" 
        , "is estimated by multiplication of upper bounds of the sub problems."] 
      , unwords [ "Note that the processor allows the optional specification of processors" 
                , "that are applied on the two individual subproblems."
                , "The transformation results into the systems which could not be oriented"
                , "by those processors." ]
      ]
    arguments _ = 
      opt { A.name         = "split" 
          , A.defaultValue = composeRCselect
          , A.description  = "This problem determines the strict rules of the selected upper congruence rules."}
      :+: 
      opt { A.name = "sub-processor-A"
          , A.defaultValue = Nothing
          , A.description = "If given, applied on the problem reflecting the upper congruence classes."
          }
      :+: 
      opt { A.name = "sub-processor-B"
          , A.defaultValue = Nothing
          , A.description = "If given, applied on the problem reflecting the lower congruence classes."
          }
    
    transform inst prob 
         | not (Prob.isDPProblem prob) = return $ T.NoProgress $ ComposeRCInapplicable "given problem is not a DP problem" 
         | otherwise = 
             do mProofA <- mapply mProcA probA
                mProofB <- case maybe True P.succeeded mProofA of 
                             True  -> mapply mProcB probB
                             False -> return Nothing
                return $ mkProof mProofA mProofB

        where s :+: mProcA :+: mProcB = T.transformationArgs inst 
              wdg = estimatedDependencyGraph Edg prob
              allLabeledNodes = lnodes wdg
              sig = Prob.signature prob

              mkProof mProofA mProofB | progress tproof = T.Progress tproof subprobs
                                      | otherwise       = T.NoProgress tproof
                  where tproof = ComposeRCProof { cpRuleSelector = s
                                                , cpUnselected   = unselectedDPs
                                                , cpSelected     = selectedStrictDPs `Trs.union` selectedWeakDPs
                                                , cpCut          = cutDPs
                                                , cpUncut        = uncutDPs
                                                , cpUnchanged    = unchangedStrictDPs `Trs.union` unchangedWeakDPs
                                                , cpProofA       = mProofA
                                                , cpProofB       = mProofB
                                                , cpProbA        = probA
                                                , cpProbB        = probB
                                                , cpWdg          = wdg
                                                , cpSig          = sig'
                                                , cpVars         = Prob.variables prob }
                        subprobs = catMaybes [ maybe (Just (SN (1 :: Int), probA)) (const Nothing) mProofA
                                             , maybe (Just (SN (2 :: Int), probB)) (const Nothing) mProofB ]

              probA = Prob.sanitise $ prob { Prob.signature = sig'
                                           , Prob.strictDPs = selectedStrictDPs
                                           , Prob.weakDPs   = Trs.unions [ cutDPs, uncutDPs, selectedWeakDPs ] }

              probB = Prob.sanitise $ prob { Prob.signature = sig'
                                           , Prob.strictDPs = uncutDPs `Trs.union` unchangedStrictDPs
                                           , Prob.weakDPs   = unchangedWeakDPs }

              
              (selectedNodes, selectedStrictDPs, selectedWeakDPs) = 
                  (Set.fromList ns, Trs.fromRules rss, Trs.fromRules rsw)
                  where (ns,rsel) = unzip selected 
                        (rss,rsw) = foldl (\ (rss',rsw') (a,r) -> 
                                           case a of 
                                             DG.StrictDP -> (r : rss',rsw')
                                             DG.WeakDP   -> (rss', r : rsw')) ([],[]) rsel
                        selected = closeBySuccessor $ rsSelect s () prob
                        closeBySuccessor rs = [(n,dpnode) | (n, dpnode) <- withNodeLabels' wdg (dfs initials wdg) ]
                            where initials = [ n | (n, (_, r)) <- allLabeledNodes, Trs.member dps r ]
                                  dps = Prob.sdp rs `Trs.union` Prob.wdp rs

              unselectedNodes          = Set.fromList (DG.nodes wdg) Set.\\ selectedNodes
              unselectedNodesWithLabel = withNodeLabels' wdg $ Set.toList unselectedNodes
              unselectedDPs            = Trs.fromRules [ r | (_,(_,r)) <- unselectedNodesWithLabel]
              ((uncutDPs, cutDPs, unchangedStrictDPs, unchangedWeakDPs), sig') = 
                  flip Sig.runSignature sig $ 
                       do ls <- mapM splitRuleM $ unselectedNodesWithLabel
                          let (unchanged, changed) = partitionEithers ls
                              unchangedStrict      = [ r | (DG.StrictDP,r) <- unchanged ]
                              unchangedWeak        = [ r | (DG.WeakDP,r)   <- unchanged ]
                              (uncuts,cuts)          = unzip changed
                              toTrs = Trs.fromRules
                          return (toTrs uncuts, toTrs cuts, toTrs unchangedStrict, toTrs unchangedWeak)
              splitRuleM (n, arl@(_,(Rule l r@(Term.Fun f ts)))) 
                  | F.isCompound sig f = mk (zip [1..] ts)
                  | otherwise          = mk (zip [1] [r])
                  where mk its 
                            | Set.null cutPositions = return $ Left arl
                            | otherwise = do uncutRule <- mkrl "" uncutTerms
                                             cutRule   <- mkrl "'" cutTerms
                                             return $ Right (uncutRule, cutRule)
                            where (uncutTerms,cutTerms) = List.partition (\ (i,_) -> i `Set.member` uncutPositions) its
                                  uncutPositions = Set.fromList [ p | (m, _, p) <- lsuccessors wdg n, not $ m `Set.member` selectedNodes ]
                                  cutPositions = Set.fromList [i | (i,_) <- its] Set.\\ uncutPositions
                                  mkrl _ [(_,t)] = return $ Rule l t
                                  mkrl sn tis    = 
                                      do attribs <- F.getAttributes f 
                                         c <- F.fresh attribs { F.symArity    = length tis
                                                             , F.symIsCompound = True 
                                                             , F.symIdent = F.symIdent attribs ++ sn}
                                         return $ Rule l (Term.Fun c [ti | (_, ti) <- tis])
              splitRuleM  (_,arl)  = return $ Left arl

              mapply :: (P.Processor p, P.SolverM m) => Maybe (P.InstanceOf p) -> Prob.Problem -> m (Maybe (P.Proof p))
              mapply Nothing      _     = return Nothing
              mapply (Just proci) probi = Just `liftM` P.apply proci probi

instance (P.Processor p1, P.Processor p2) => T.TransformationProof (ComposeRC p1 p2) where
    pprintTProof _ _ (ComposeRCInapplicable reason) = text "Compose RC is inapplicable since" <+> text reason
    pprintTProof _ prob tproof = text "We measure the number of applications of following selected rules relative to the remaining rules"
                                $+$ text ""
                                $+$ indent (pptrs "Selected Rules (A)" (cpSelected tproof))
                                $+$ indent (pptrs "Remaining Rules (B)" (cpUnselected tproof))
                                $+$ text ""
                                $+$ (text "These ruleset (A) was choosen by selecting function" 
                                     <+> quotes (text (show (cpRuleSelector tproof))) <> text ","
                                     <+> text "and closed under successors in the dependency graph.")
                                $+$ text "The length of a single A-subderivation is expressed by the following problem."
                                $+$ text ""
                                $+$ block' "Problem A" [pprint (cpProbA tproof)]
                                $+$ text ""
                                $+$ text "The number of B-applications is expressed by the following problem."
                                $+$ text ""
                                $+$ block' "Problem B" [pprint (cpProbB tproof)]
                                $+$ maybePrintSub (cpProofA tproof) "A"
                                $+$ maybePrintSub (cpProofB tproof) "B"
       where sig = cpSig tproof
             vars = Prob.variables prob
             pptrs = pprintNamedTrs sig vars
             maybePrintSub :: P.Processor p => Maybe (P.Proof p) -> String -> Doc
             maybePrintSub Nothing  _ = empty
             maybePrintSub (Just p) n | P.succeeded p = text ""
                                                        $+$ text "We first check Problem" <+> text n <> text ":"
                                                        $+$ indent (P.pprintProof p P.ProofOutput)
                                      | otherwise     = text "We did not obtain a certificate for Problem" <+> text n
                                                        $+$ text "We abort."

    answer proof = 
      case tproof of 
        ComposeRCInapplicable{} -> P.MaybeAnswer
        _ -> 
          case ub of
            Cert.Unknown -> P.MaybeAnswer
            _            -> P.CertAnswer $ Cert.certified (lb, ub)
        where tproof = T.transformationProof proof
              subproofs = T.subProofs proof
              ub = Cert.upperBound cert1 `Cert.mult` Cert.upperBound cert2
              lb = Cert.lowerBound cert1 `Cert.add` Cert.lowerBound cert2
              cert1 = certFrom (cpProofA tproof) (find (1 :: Int) subproofs)
              cert2 = certFrom (cpProofB tproof) (find (2 :: Int) subproofs)
              certFrom :: (P.ComplexityProof a1, P.ComplexityProof a2) => Maybe a1 -> Maybe a2 -> Cert.Certificate
              certFrom mp1 mp2 = maybe Cert.uncertified id mcert 
                  where mcert = (P.certificate `liftM` mp1) `mplus` (P.certificate `liftM` mp2)


-- | This is the default 'RuleSelector' used with 'composeRC'.
composeRCselect :: RuleSelector a
composeRCselect = selFromWDG "below first cut in WDG" fn
    where fn _ dg = Prob.emptyRuleset { Prob.sdp = Trs.fromRules [r | (DG.StrictDP,r) <- selectedRules ]
                                      , Prob.wdp = Trs.fromRules [r | (DG.WeakDP,r) <- selectedRules ] }
              where dgclosure = trc dg
                    reachables = Gr.suc dgclosure 
                    n `pathTo` m = m `elem` reachables n
                    nonCutEdges n = Set.fromList [ i | (m,_,i) <- DG.lsuccessors dg n, m `pathTo` n ]
                    cutEdges n =    Set.fromList [ i | (_,_,i) <- DG.lsuccessors dg n, not (i `Set.member` nonCutEdges n) ]
                    admitCuts = [ n | n <- DG.nodes dg , not (Set.null $ cutEdges n) && not (Set.null $ nonCutEdges n) ]
                    highestCuts = snub $ concatMap (DG.congruence cdg) $ DG.roots cdg
                        where cdg = DG.toCongruenceGraph $ DG.subGraph dg admitCuts
--                    highestCuts = [ n | n <- admitCuts , not (any (\ m -> m /= n && m `pathTo` n) admitCuts) ]
                    selectedNodes = intersects [ Set.fromList [ m | (m,_,i) <- DG.lsuccessors dg n, i `Set.member` cutEdges n] | n <- highestCuts ]
                        where intersects = foldl Set.union Set.empty
                    selectedRules = map snd $ DG.withNodeLabels' dg (Set.toList selectedNodes)


composeRCProcessor :: T.Transformation (ComposeRC P.AnyProcessor P.AnyProcessor) P.AnyProcessor
composeRCProcessor = T.Transformation ComposeRC

-- | This processor implements processor \'compose\' specifically for
-- the (weak) dependency pair setting. It tries to estimate the
-- complexity of the input problem based on the complexity of
-- dependency pairs of upper congruence classes (with respect to the
-- congruence graph) relative to the dependency pairs in the remaining
-- lower congruence classes. The overall upper bound for the
-- complexity of the input problem is estimated by multiplication of
-- upper bounds of the sub problems.
-- Note that the processor allows the optional specification of
-- processors that are applied on the two individual subproblems. The
-- transformation results into the systems which could not be oriented
-- by those processors.
composeRC :: RuleSelector () -> T.TheTransformer (ComposeRC P.AnyProcessor P.AnyProcessor)
composeRC s = T.Transformation ComposeRC `T.withArgs` (s :+: Nothing :+: Nothing)

-- | Specify a processor to solve Problem A immediately. 
-- The Transformation aborts if the problem cannot be handled.
solveAWith :: (P.Processor p1, P.Processor p2, P.Processor p) => (T.TheTransformer (ComposeRC p1 p2)) -> P.InstanceOf p -> (T.TheTransformer (ComposeRC p p2))
solveAWith (T.TheTransformer _ (s :+: _ :+: p2)) p = T.TheTransformer ComposeRC (s :+: Just p :+: p2)

-- | Specify a processor to solve Problem B immediately. 
-- The Transformation aborts if the problem cannot be handled.
solveBWith :: (P.Processor p1, P.Processor p2, P.Processor p) => (T.TheTransformer (ComposeRC p1 p2)) -> P.InstanceOf p -> (T.TheTransformer (ComposeRC p1 p))
solveBWith (T.TheTransformer _ (s :+: p1 :+: _)) p = T.TheTransformer ComposeRC (s :+: p1 :+: Just p)