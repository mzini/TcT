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
         decomposeDG
       , solveUpperWith
       , solveLowerWith         
       , selectLowerBy
       , decomposeDGselect
         -- * Proof Object
       , DecomposeDGProof (..)
         -- * Processor
       , decomposeDGProcessor
       , DecomposeDG
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

import Termlib.Utils (PrettyPrintable (..), paragraph)
import qualified Termlib.Term as Term
import qualified Termlib.Trs as Trs
import Termlib.Rule (Rule(..))
import qualified Termlib.FunctionSymbol as F
import qualified Termlib.Problem as Prob
import qualified Tct.Method.DP.DependencyGraph as DG
import Tct.Method.RuleSelector
import Data.Graph.Inductive.Query.DFS (dfs)
import Data.Typeable ()
import Termlib.Utils (snub) 

data DecomposeDG p1 p2 = DecomposeDG
data DecomposeDGProof p1 p2 = DecomposeDGProof 
                              { cpRuleSelector   :: ExpressionSelector
                              , cpUnselected     :: Trs.Trs
                              , cpSelected       :: Trs.Trs 
                              , cpExtensionRules :: Trs.Trs
                              , cpProofD         :: Maybe (P.Proof p1) 
                              , cpProofU         :: Maybe (P.Proof p2)
                              , cpProbD          :: Prob.Problem
                              , cpProbU          :: Prob.Problem
                              , cpWdg            :: DG.DG}
                          | DecomposeDGInapplicable String

progress :: (P.Processor p1, P.Processor p2) => DecomposeDGProof p1 p2 -> Bool
progress DecomposeDGInapplicable {} = False
progress proof = maybe True P.succeeded (cpProofD proof) 
                 && maybe True P.succeeded (cpProofU proof)
                 && not (Trs.isEmpty sdps)
   where sdps = Prob.strictDPs $ cpProbU proof
         

instance (P.Processor p1, P.Processor p2) => T.Transformer (DecomposeDG p1 p2) where
    type ArgumentsOf (DecomposeDG p1 p2) = Arg (Assoc (ExpressionSelector)) :+: Arg (Maybe (Proc p1)) :+: Arg (Maybe (Proc p2))
    type ProofOf (DecomposeDG p1 p2)     = DecomposeDGProof p1 p2

    name _ = "decomposeDG"
    instanceName inst = show $ text "decomposeDG" <+> parens (ppsplit)
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
          , A.defaultValue = decomposeDGselect
          , A.description  = "This problem determines the strict rules of the selected upper congruence rules."}
      :+: 
      opt { A.name = "sub-processor-A"
          , A.defaultValue = Nothing
          , A.description = "Use this processor to solve the upper component."
          }
      :+: 
      opt { A.name = "sub-processor-B"
          , A.defaultValue = Nothing
          , A.description = "Use this processor to solve the lower component."
          }
    
    transform inst prob 
         | not (Prob.isDPProblem prob) = return $ T.NoProgress $ DecomposeDGInapplicable "given problem is not a DP problem" 
         | not (Trs.isEmpty $ Prob.strictTrs prob) = return $ T.NoProgress $ DecomposeDGInapplicable "strict rules of input problem are empty" 
         | Trs.isEmpty initialDPs  = return $ T.NoProgress $ DecomposeDGInapplicable "no rules were selected" 
         | not (any isCut unselectedNodes) = return $ T.NoProgress $ DecomposeDGInapplicable "no rule was cut"
         | prob `subsetDP` probA = return $ T.NoProgress $ DecomposeDGInapplicable "lower component not simpler"
         | otherwise = 
             do mProofA <- mapply mProcA probA
                mProofB <- case maybe True P.succeeded mProofA of 
                             True  -> mapply mProcB probB
                             False -> return Nothing
                return $ mkProof mProofA mProofB

        where s :+: mProcA :+: mProcB = T.transformationArgs inst 
              wdg = DG.estimatedDependencyGraph DG.defaultApproximation prob
              allLabeledNodes = DG.lnodes wdg
              sig = Prob.signature prob

              mkProof mProofA mProofB 
                  | progress tproof = T.Progress tproof subprobs
                  | otherwise       = T.NoProgress tproof
                  where 
                    tproof = DecomposeDGProof 
                             { cpRuleSelector   = s
                             , cpUnselected     = Trs.fromRules [ r | (_,(_,r)) <- unselectedLabeledNodes]
                             , cpSelected       = selectedStrictDPs `Trs.union` selectedWeakDPs
                             , cpExtensionRules = extRules
                             , cpProofD         = mProofA
                             , cpProofU         = mProofB
                             , cpProbD          = probA
                             , cpProbU          = probB
                             , cpWdg            = wdg }
                    subprobs = catMaybes [ maybe (Just (SN (1 :: Int), probA)) (const Nothing) mProofA
                                         , maybe (Just (SN (2 :: Int), probB)) (const Nothing) mProofB ]

              extRules = flatten unselectedStrictDPs `Trs.union` flatten unselectedWeakDPs

              probA = Prob.sanitise $ 
                 prob { Prob.strictDPs = selectedStrictDPs
                      , Prob.weakDPs   = extRules `Trs.union` selectedWeakDPs }

              probB = Prob.sanitise $ 
                 prob { Prob.strictDPs = unselectedStrictDPs
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
                        closeBySuccessor rs = [(n,dpnode) | (n, dpnode) <- DG.withNodeLabels' wdg (dfs initials wdg) ]
                            where initials = [ n | (n, (_, r)) <- allLabeledNodes, rs `Trs.member` r ]

              unselectedNodes = [n | n <- DG.nodes wdg, not (n `Set.member` selectedNodes)]

              isCut n = any (`Set.member` selectedNodes) (DG.successors wdg n)

              unselectedLabeledNodes = DG.withNodeLabels' wdg $ unselectedNodes
              (cutWeakDPs, uncutWeakDPs) = List.partition (\ (n,_) -> isCut n) [ (n,r) | (n,(DG.WeakDP, r)) <- unselectedLabeledNodes ]
              unselectedStrictDPs = Trs.fromRules $ [ r | (_,(DG.StrictDP, r)) <- unselectedLabeledNodes ] 
                                                    ++ [ r | (_, r) <- cutWeakDPs]
              unselectedWeakDPs = Trs.fromRules [ r | (_, r) <- uncutWeakDPs]

              prob1 `subsetDP` prob2 = 
                  all (Trs.member $ Prob.strictDPs prob2) (Trs.toRules $ Prob.strictDPs prob1)
                  && all (Trs.member $ Prob.weakDPs prob2) (Trs.toRules $ Prob.weakDPs prob1)
               

              mapply :: (P.Processor p, P.SolverM m) => Maybe (P.InstanceOf p) -> Prob.Problem -> m (Maybe (P.Proof p))
              mapply Nothing      _     = return Nothing
              mapply (Just proci) probi = Just `liftM` P.apply proci probi

instance (P.Processor p1, P.Processor p2) => T.TransformationProof (DecomposeDG p1 p2) where
    pprintTProof _ _ (DecomposeDGInapplicable reason) _ = text "Dependency graph decomposition is inapplicable since" <+> text reason <> text "."
    pprintTProof _ prob tproof mde = 
      paragraph "We decompose the input problem according to the dependency graph into the upper component"
      $+$ text ""
      $+$ indent (pprint (cpUnselected tproof, sig, vars))
      $+$ text ""
      $+$ paragraph "and lower component"
      $+$ text ""
      $+$ indent (pprint (cpSelected tproof, sig, vars))
      $+$ text ""
      $+$ paragraph "Further, following extension rules are added to the lower component."
      $+$ text ""
      $+$ pprint (cpExtensionRules tproof, sig, vars)
      $+$ maybePrintSub (cpProofD tproof) "lower"
      $+$ maybePrintSub (cpProofU tproof) "upper"
       where 
         vars = Prob.variables prob
         sig  = Prob.signature prob
         maybePrintSub :: P.Processor p => Maybe (P.Proof p) -> String -> Doc
         maybePrintSub Nothing  _ = empty
         maybePrintSub (Just p) n = 
           text ""
           $+$ paragraph (show ppAns)
           $+$ text ""
           $+$ block' "Sub-proof" [P.pprintProof p mde]
           $+$ text ""
           $+$ text "We return to the main proof."
           where 
             ppAns
               | P.succeeded p = 
                   text "TcT solves the" <+> text n <+> text "component with certificate" 
                   <+> pprint (P.answer p) <> text "."
               | otherwise =
                   text "TcT could not construct a certificate for the"
                   <+> text n <+> text "component. We abort."
    answer proof = 
      case tproof of 
        DecomposeDGInapplicable{} -> P.MaybeAnswer
        _ -> 
          case ub of
            Cert.Unknown -> P.MaybeAnswer
            _            -> P.CertAnswer $ Cert.certified (lb, ub)
        where tproof = T.transformationProof proof
              subproofs = T.subProofs proof
              ub = Cert.upperBound cert1 `Cert.mult` Cert.upperBound cert2
              lb = Cert.lowerBound cert1 `Cert.add` Cert.lowerBound cert2
              cert1 = certFrom (cpProofD tproof) (find (1 :: Int) subproofs)
              cert2 = certFrom (cpProofU tproof) (find (2 :: Int) subproofs)
              certFrom :: (P.ComplexityProof a1, P.ComplexityProof a2) => Maybe a1 -> Maybe a2 -> Cert.Certificate
              certFrom mp1 mp2 = maybe Cert.uncertified id mcert 
                  where mcert = (P.certificate `liftM` mp1) `mplus` (P.certificate `liftM` mp2)


-- | This is the default 'RuleSelector' used with 'decomposeDG'.
decomposeDGselect :: ExpressionSelector
decomposeDGselect = selAllOf (selFromWDG f) { rsName = "below first cut in WDG" }
  where f wdg = 
          Prob.emptyRuleset { Prob.sdp = Trs.fromRules [r | (DG.StrictDP,r) <- selectedRules ]
                            , Prob.wdp = Trs.fromRules [r | (DG.WeakDP,r) <- selectedRules ]}
          where 
            cwdg = DG.toCongruenceGraph wdg
            selectedRules = DG.allRulesFromNodes cwdg (snub $ concat $ [DG.successors cwdg n | n <-  Set.toList cutNodes])
            cutNodes = Set.unions [ cutNodesFrom r (cyclic r) | r <- DG.roots cwdg ] 
              where 
                cyclic = DG.isCyclicNode cwdg
                
                cutNodesFrom n isCyclic
                  | isCutCongruence n = Set.singleton n
                  | otherwise = Set.unions [ cutNodesFrom m (isCyclic || cyclic m) | m <- DG.successors cwdg n ]
                isCutCongruence n = any isCut ms
                  where ms = [ m | (m,_) <- DG.theSCC $ DG.lookupNodeLabel' cwdg n ]
                        isCut m = not $ null $ 
                                  [ (m1,m2) | (m1, _, i) <- lsuccs
                                            , m1 `elem` ms
                                            , (m2, _, j) <- lsuccs
                                            , i /= j                                                                           
                                            , m2 `notElem` ms ]
                          where lsuccs = DG.lsuccessors wdg m
-- decomposeDGselect = selAllOf $ selFromWDG "below first cut in WDG" fn
--     where fn dg = Prob.emptyRuleset { Prob.sdp = Trs.fromRules [r | (StrictDP,r) <- selectedRules ]
--                                     , Prob.wdp = Trs.fromRules [r | (WeakDP,r) <- selectedRules ]}
--               where nonCutEdges n = Set.fromList [ i | (m,_,i) <- DG.lsuccessors dg n, n `elem` DG.reachablesBfs dg [m] ]
--                     cutEdges n =    Set.fromList [ i | (_,_,i) <- DG.lsuccessors dg n, not (i `Set.member` nonCutEdges n) ]
--                     admitCuts = [ n | n <- DG.nodes dg , not (Set.null $ cutEdges n) && not (Set.null $ nonCutEdges n) ]
--                     highestCuts = snub $ concatMap (DG.congruence subcdg) $ DG.roots subcdg
--                     subcdg = DG.toCongruenceGraph $ DG.subGraph dg admitCuts
--                     selectedNodes = Set.unions [ Set.fromList [ m | (m,_,i) <- DG.lsuccessors dg n, i `Set.member` cutEdges n] | n <- highestCuts ]
--                     selectedRules = map snd $ DG.withNodeLabels' dg (Set.toList selectedNodes)


decomposeDGProcessor :: T.Transformation (DecomposeDG P.AnyProcessor P.AnyProcessor) P.AnyProcessor
decomposeDGProcessor = T.Transformation DecomposeDG

-- | This processor implements processor \'dependency graph decomposition\'. 
-- It tries to estimate the
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
decomposeDG :: T.TheTransformer (DecomposeDG P.AnyProcessor P.AnyProcessor)
decomposeDG = T.Transformation DecomposeDG `T.withArgs` (decomposeDGselect :+: Nothing :+: Nothing)

-- | Specify a processor to solve the lower immediately. 
-- The Transformation aborts if the problem cannot be handled.
solveLowerWith :: (P.Processor p1, P.Processor p2, P.Processor p) => (T.TheTransformer (DecomposeDG p1 p2)) -> P.InstanceOf p -> (T.TheTransformer (DecomposeDG p p2))
solveLowerWith (T.TheTransformer _ (s :+: _ :+: p2)) p = T.TheTransformer DecomposeDG (s :+: Just p :+: p2)

-- | Specify a processor to solve the upper component immediately.
-- The Transformation aborts if the problem cannot be handled.
solveUpperWith :: (P.Processor p1, P.Processor p2, P.Processor p) => (T.TheTransformer (DecomposeDG p1 p2)) -> P.InstanceOf p -> (T.TheTransformer (DecomposeDG p1 p))
solveUpperWith (T.TheTransformer _ (s :+: p1 :+: _)) p = T.TheTransformer DecomposeDG (s :+: p1 :+: Just p)

-- | Specify how the lower component should be selected.
selectLowerBy :: (P.Processor p1, P.Processor p2) => (T.TheTransformer (DecomposeDG p1 p2)) -> RuleSelector SelectorExpression -> (T.TheTransformer (DecomposeDG p1 p2))
selectLowerBy (T.TheTransformer _ (_ :+: p1 :+: p2)) s = T.TheTransformer DecomposeDG (s :+: p1 :+: p2)