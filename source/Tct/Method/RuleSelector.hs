{-# LANGUAGE DeriveDataTypeable #-}

{- | 
Module      :  Tct.Method.RuleSelector
Copyright   :  (c) Martin Avanzini <martin.avanzini@uibk.ac.at>, 
               Georg Moser <georg.moser@uibk.ac.at>, 
               Andreas Schnabl <andreas.schnabl@uibk.ac.at>
License     :  LGPL (see COPYING)

Maintainer  :  Martin Avanzini <martin.avanzini@uibk.ac.at>
Stability   :  unstable
Portability :  unportable      

Rule selectors give a general method to select rules from a problem.
-}

module Tct.Method.RuleSelector 
       (
         -- | A 'RuleSelector' is used to select 
         -- rules from a problem. Various combinators 
         -- are implemented.
       RuleSelector (..)
       , selRules
       , selDPs
       , selStricts
       , selWeaks
         -- * Rule-selectors based on dependency graphs
       , selFromWDG
       , selFromCWDG
       , selFirstCongruence
       , selFirstStrictCongruence
         -- * Combinators
       , selCombine 
       , selInverse
       , selUnion
       , selInter
       ) where

import Data.Typeable (Typeable)
import Tct.Method.DP.DependencyGraph
import Data.Graph.Inductive.Query.BFS (bfsn)
import qualified Tct.Method.DP.DependencyGraph as DG
import qualified Termlib.Problem as Prob
import qualified Termlib.Trs as Trs
import Termlib.Problem (Problem)


-- | This datatype is used to select a subset of rules recorded in a problem.
data RuleSelector a = RS { rsName :: String -- ^ Name of the rule selector.
                         , rsSelect :: a -> Problem -> Prob.Ruleset -- ^ Given state 'a' and problem, select a 'Prob.Ruleset' from the problem
                                                                 -- ^ whose TRSs should be subsets of the TRSs from the input problem.
                         } deriving Typeable

instance Show (RuleSelector a) where show = rsName


-- | Inverses the selection.
selInverse :: RuleSelector a -> RuleSelector a
selInverse s = RS { rsName = "inverse of " ++ rsName s
                  , rsSelect = fn }
    where fn a prob = Prob.Ruleset { Prob.sdp  = inv Prob.strictDPs Prob.sdp
                                   , Prob.wdp  = inv Prob.weakDPs Prob.wdp
                                   , Prob.strs = inv Prob.strictTrs Prob.strs
                                   , Prob.wtrs = inv Prob.weakTrs Prob.wtrs }
              where rs = rsSelect s a prob
                    inv pfn rfn = pfn prob Trs.\\ rfn rs

-- | Combine two rule-selectors component-wise.
selCombine :: (String -> String -> String) -> (Trs.Trs -> Trs.Trs -> Trs.Trs) -> (RuleSelector a -> RuleSelector a -> RuleSelector a)
selCombine cn ctrs s1 s2 = RS { rsName = cn (rsName s1) (rsName s2)
                              , rsSelect = fn }
        where fn a prob = Prob.Ruleset { Prob.sdp  = un Prob.sdp
                                       , Prob.wdp  = un Prob.wdp
                                       , Prob.strs = un Prob.strs
                                       , Prob.wtrs = un Prob.wtrs }
                  where rs1 = rsSelect s1 a prob
                        rs2 = rsSelect s2 a prob
                        un rfn = rfn rs1 `ctrs` rfn rs2

-- | Select union of selections of given rule-selectors.
selUnion :: RuleSelector a -> RuleSelector a -> RuleSelector a
selUnion = selCombine (\ n1 n2 -> "union of " ++ n1 ++ " and " ++ n2) Trs.union

-- | Select intersection of selections of given rule-selectors.
selInter :: RuleSelector a -> RuleSelector a -> RuleSelector a
selInter= selCombine (\ n1 n2 -> "intersect of " ++ n1 ++ " and " ++ n2) Trs.intersect


-- | Select rewrite rules, i.e., non dependency pair rules.
selRules :: RuleSelector a
selRules = RS { rsName   = "rewrite-rules" , rsSelect = fn } 
    where fn _ prob = Prob.Ruleset { Prob.sdp = Trs.empty
                                   , Prob.wdp = Trs.empty
                                   , Prob.strs = Prob.strictTrs prob
                                   , Prob.wtrs = Prob.weakTrs prob }
           
-- | Select dependency pairs.
selDPs :: RuleSelector a
selDPs = RS { rsName = "DPs" , rsSelect = fn }
    where fn _ prob = Prob.Ruleset { Prob.sdp = Prob.strictDPs prob
                                   , Prob.wdp = Prob.weakDPs prob
                                   , Prob.strs = Trs.empty
                                   , Prob.wtrs = Trs.empty }

-- | Select strict rules.
selStricts :: RuleSelector a
selStricts = RS { rsName = "strict-rules" , rsSelect = fn }
    where fn _ prob = Prob.Ruleset { Prob.sdp = Prob.strictDPs prob
                                   , Prob.wdp = Trs.empty
                                   , Prob.strs = Prob.strictTrs prob
                                   , Prob.wtrs = Trs.empty }

-- | Select strict rules.
selWeaks :: RuleSelector a
selWeaks = RS { rsName = "weak-rules" , rsSelect = fn }
    where fn _ prob = Prob.Ruleset { Prob.sdp = Trs.empty
                                   , Prob.wdp = Prob.weakDPs prob
                                   , Prob.strs = Trs.empty
                                   , Prob.wtrs = Prob.weakTrs prob }

-- | Select from the dependency graph, using the given function. 
-- The first parameter should specify a short name for the rule-selector.
selFromWDG :: String -> (a -> DG -> Prob.Ruleset) -> RuleSelector a
selFromWDG n f = RS { rsName = n
                    , rsSelect = \a prob -> f a (dg prob) }
    where dg = estimatedDependencyGraph Edg

-- | Select from the congruence dependency graph, using the given function.
-- The first parameter should specify a short name for the rule-selector.          
selFromCWDG :: String -> (a -> CDG -> Prob.Ruleset) -> RuleSelector a
selFromCWDG n f = RS { rsName = n
                     , rsSelect = \a prob -> f a (dg prob) }
    where dg = toCongruenceGraph . estimatedDependencyGraph Edg

restrictToCongruences :: Prob.Ruleset -> [NodeId] -> CDG -> Prob.Ruleset
restrictToCongruences rs ns cdg = rs { Prob.sdp = Trs.fromRules [ r | (DG.StrictDP, r) <- rr]
                                     , Prob.wdp = Trs.fromRules [ r | (DG.WeakDP, r) <- rr] }
    where rr = allRulesFromNodes cdg ns

-- | Selects all rules from root-nodes in the congruence graph.
selFirstCongruence :: RuleSelector a
selFirstCongruence = selFromCWDG "first congruence from CWDG" fn
    where fn _ cdg = restrictToCongruences Prob.emptyRuleset (roots cdg) cdg 

-- | Selects all rules from nodes @n@ of the CWDG that satisfy
-- (i) the node @n@ references at least one strict rule, and (ii)
-- there is no node between a root of the CWDG and @n@ containing a strict rule.
selFirstStrictCongruence :: RuleSelector a
selFirstStrictCongruence = selFromCWDG "first congruence with strict rules from CWDG" fn
    where fn _ cdg = restrictToCongruences Prob.emptyRuleset ns cdg 
              where ns = take 1 $ [ n | n <- bfsn (roots cdg) cdg
                                  , any ((==) DG.StrictDP . fst) (allRulesFromNodes cdg [n])  ]
