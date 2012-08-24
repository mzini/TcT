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
import Termlib.Utils (PrettyPrintable (..), paragraph, snub)
import qualified Termlib.Term as Term
import qualified Termlib.Trs as Trs
import Termlib.Rule (Rule(..))
import qualified Termlib.FunctionSymbol as F
import qualified Termlib.Problem as Prob
import Tct.Method.DP.DependencyGraph
import qualified Tct.Method.DP.DependencyGraph as DG
import Tct.Method.RuleSelector
import Data.Graph.Inductive.Query.DFS (dfs)
import Data.Typeable ()

data ComposeRC p1 p2 = ComposeRC
data ComposeRCProof p1 p2 = ComposeRCProof { cpRuleSelector :: ExpressionSelector
                                           , cpUnselected   :: Trs.Trs
                                           , cpSelected     :: Trs.Trs 
                                           , cpProofA       :: Maybe (P.Proof p1) 
                                           , cpProofB       :: Maybe (P.Proof p2)
                                           , cpProbA        :: Prob.Problem
                                           , cpProbB        :: Prob.Problem
                                           , cpWdg          :: DG.DG}
                          | ComposeRCInapplicable String

progress :: (P.Processor p1, P.Processor p2) => ComposeRCProof p1 p2 -> Bool
progress ComposeRCInapplicable {} = False
progress proof = maybe True P.succeeded (cpProofA proof) 
                 && maybe True P.succeeded (cpProofB proof)
                 && not (Trs.isEmpty sdps)
   where sdps = Prob.strictDPs $ cpProbB proof
         

instance (P.Processor p1, P.Processor p2) => T.Transformer (ComposeRC p1 p2) where
    type ArgumentsOf (ComposeRC p1 p2) = Arg (Assoc (ExpressionSelector)) :+: Arg (Maybe (Proc p1)) :+: Arg (Maybe (Proc p2))
    type ProofOf (ComposeRC p1 p2)     = ComposeRCProof p1 p2

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
         | not (Trs.isEmpty $ Prob.strictTrs prob) = return $ T.NoProgress $ ComposeRCInapplicable "strict rules of input problem are empty" 
         | Trs.isEmpty initialDPs  = return $ T.NoProgress $ ComposeRCInapplicable "no was rules selected" 
         | otherwise = 
             do mProofA <- mapply mProcA probA
                mProofB <- case maybe True P.succeeded mProofA of 
                             True  -> mapply mProcB probB
                             False -> return Nothing
                return $ mkProof mProofA mProofB

        where s :+: mProcA :+: mProcB = T.transformationArgs inst 
              wdg = estimatedDependencyGraph DG.defaultApproximation prob
              allLabeledNodes = lnodes wdg
              sig = Prob.signature prob

              mkProof mProofA mProofB | progress tproof = T.Progress tproof subprobs
                                      | otherwise       = T.NoProgress tproof
                  where tproof = ComposeRCProof { cpRuleSelector = s
                                                , cpUnselected   = Trs.fromRules [ r | (_,(_,r)) <- unselectedLabeledNodes]
                                                , cpSelected     = selectedStrictDPs `Trs.union` selectedWeakDPs
                                                , cpProofA       = mProofA
                                                , cpProofB       = mProofB
                                                , cpProbA        = probA
                                                , cpProbB        = probB
                                                , cpWdg          = wdg }
                        subprobs = catMaybes [ maybe (Just (SN (1 :: Int), probA)) (const Nothing) mProofA
                                             , maybe (Just (SN (2 :: Int), probB)) (const Nothing) mProofB ]

              probA = Prob.sanitise $ prob { Prob.strictDPs = selectedStrictDPs
                                           , Prob.weakDPs   = Trs.unions [ flatten unselectedStrictDPs
                                                                         , flatten unselectedWeakDPs
                                                                         , selectedWeakDPs ] }

              probB = Prob.sanitise $ prob { Prob.strictDPs = unselectedStrictDPs
                                           , Prob.weakDPs   = unselectedWeakDPs }

              flatten = Trs.fromRules . concatMap flattenRule . Trs.toRules
                 where flattenRule (Rule l (Term.Fun f ts))
                           | F.isCompound sig f = [ Rule l ti | ti <- ts ]
                       flattenRule (Rule l r) = [ Rule l r ]
              
              initialDPs = fst $ rules $ rsSelect (selFirstAlternative s) prob
              (selectedNodes, selectedStrictDPs, selectedWeakDPs) = 
                  (Set.fromList ns, Trs.fromRules rss, Trs.fromRules rsw)
                  where (ns,rsel) = unzip selected 
                        (rss,rsw) = foldl separate ([],[]) rsel
                            where separate (stricts,weaks) (DG.StrictDP,r) = (r : stricts,weaks)
                                  separate (stricts,weaks) (DG.WeakDP,r)   = (stricts,r : weaks)
                        selected = closeBySuccessor $ initialDPs
                        closeBySuccessor rs = [(n,dpnode) | (n, dpnode) <- withNodeLabels' wdg (dfs initials wdg) ]
                            where initials = [ n | (n, (_, r)) <- allLabeledNodes, rs `Trs.member` r ]

              unselectedLabeledNodes = DG.withNodeLabels' wdg $ Set.toList $ Set.fromList (DG.nodes wdg) Set.\\ selectedNodes
              (cutWeakDPs, uncutWeakDPs) = List.partition isCut [ (n,r) | (n,(DG.WeakDP, r)) <- unselectedLabeledNodes ]
                    where isCut (n, _) = any (`Set.member` selectedNodes) (successors wdg n)
              unselectedStrictDPs = Trs.fromRules $ [ r | (_,(DG.StrictDP, r)) <- unselectedLabeledNodes ] 
                                                    ++ [ r | (_, r) <- cutWeakDPs]
              unselectedWeakDPs = Trs.fromRules [ r | (_, r) <- uncutWeakDPs]

              
              mapply :: (P.Processor p, P.SolverM m) => Maybe (P.InstanceOf p) -> Prob.Problem -> m (Maybe (P.Proof p))
              mapply Nothing      _     = return Nothing
              mapply (Just proci) probi = Just `liftM` P.apply proci probi

instance (P.Processor p1, P.Processor p2) => T.TransformationProof (ComposeRC p1 p2) where
    pprintTProof _ _ (ComposeRCInapplicable reason) _ = text "Compose RC is inapplicable since" <+> text reason <> text "."
    pprintTProof _ prob tproof _ = 
      paragraph "We measure the number of applications of following selected rules relative to the remaining rules."
      $+$ text ""
      $+$ indent (pptrs "Selected Rules (A)" (cpSelected tproof))
      $+$ indent (pptrs "Remaining Rules (B)" (cpUnselected tproof))
      $+$ text ""
      $+$ paragraph "The length of a single A-subderivation is expressed by the following problem."
      $+$ text ""
      $+$ block' "Problem (A)" [pprint (cpProbA tproof)]
      $+$ text ""
      $+$ paragraph "The number of B-applications is expressed by the following problem."
      $+$ text ""
      $+$ block' "Problem (B)" [pprint (cpProbB tproof)]
      $+$ maybePrintSub (cpProofA tproof) "A"
      $+$ maybePrintSub (cpProofB tproof) "B"
       where vars = Prob.variables prob
             sig  = Prob.signature prob
             pptrs = pprintNamedTrs sig vars
             maybePrintSub :: P.Processor p => Maybe (P.Proof p) -> String -> Doc
             maybePrintSub Nothing  _ = empty
             maybePrintSub (Just p) n = 
               case P.succeeded p of 
                 True -> text ""
                         $+$ paragraph ("TcT answers on problem (" ++ n ++ ") " 
                                        ++ show (pprint (P.answer p)) ++ ".")
                 False -> paragraph ("Unfortnuately TcT could not construct a certificate for Problem ("
                                     ++ show n ++ "). We abort.")
               $+$ text ""
               $+$ block' "Sub-proof" [P.pprintProof p P.ProofOutput]

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
composeRCselect :: ExpressionSelector
-- composeRCselect = selAllOf $ selFromCWDG "below first cut in CWDG" fn
--   where fn cwdg = 
--           case DG.roots cwdg of 
--             (r:_) -> selBelow cwdg r
--             _ -> Prob.emptyRuleset
--         selBelow cwdg r = Prob.emptyRuleset { Prob.sdp = Trs.fromRules [ rl | (DG.StrictDP, rl) <- rs ]
--                                             , Prob.wdp = Trs.fromRules [ rl | (DG.WeakDP, rl) <- rs ] }
--           where rs = DG.allRulesFromNodes cwdg strictSuccs
--                 strictSuccs = [ n | n <- DG.successors cwdg r
--                                   , any (\ (s,_) -> s == DG.StrictDP) $ DG.allRulesFromNodes cwdg $ DG.reachablesDfs cwdg [n] ]
composeRCselect = selAllOf $ selFromWDG "below first cut in WDG" fn
    where fn dg = Prob.emptyRuleset { Prob.sdp = Trs.fromRules [r | (StrictDP,r) <- selectedRules ]
                                    , Prob.wdp = Trs.fromRules [r | (WeakDP,r) <- selectedRules ]}
              where nonCutEdges n = Set.fromList [ i | (m,_,i) <- DG.lsuccessors dg n, n `elem` DG.reachablesBfs dg [m] ]
                    cutEdges n =    Set.fromList [ i | (_,_,i) <- DG.lsuccessors dg n, not (i `Set.member` nonCutEdges n) ]
                    admitCuts = [ n | n <- DG.nodes dg , not (Set.null $ cutEdges n) && not (Set.null $ nonCutEdges n) ]
                    highestCuts = snub $ concatMap (DG.congruence subcdg) $ DG.roots subcdg
                    subcdg = DG.toCongruenceGraph $ DG.subGraph dg admitCuts
                    selectedNodes = Set.unions [ Set.fromList [ m | (m,_,i) <- DG.lsuccessors dg n, i `Set.member` cutEdges n] | n <- highestCuts ]
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
composeRC :: ExpressionSelector -> T.TheTransformer (ComposeRC P.AnyProcessor P.AnyProcessor)
composeRC s = T.Transformation ComposeRC `T.withArgs` (s :+: Nothing :+: Nothing)

-- | Specify a processor to solve Problem A immediately. 
-- The Transformation aborts if the problem cannot be handled.
solveAWith :: (P.Processor p1, P.Processor p2, P.Processor p) => (T.TheTransformer (ComposeRC p1 p2)) -> P.InstanceOf p -> (T.TheTransformer (ComposeRC p p2))
solveAWith (T.TheTransformer _ (s :+: _ :+: p2)) p = T.TheTransformer ComposeRC (s :+: Just p :+: p2)

-- | Specify a processor to solve Problem B immediately. 
-- The Transformation aborts if the problem cannot be handled.
solveBWith :: (P.Processor p1, P.Processor p2, P.Processor p) => (T.TheTransformer (ComposeRC p1 p2)) -> P.InstanceOf p -> (T.TheTransformer (ComposeRC p1 p))
solveBWith (T.TheTransformer _ (s :+: p1 :+: _)) p = T.TheTransformer ComposeRC (s :+: p1 :+: Just p)