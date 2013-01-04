{-# LANGUAGE FlexibleInstances #-}
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
       SelectorExpression (..)
         -- | A 'RuleSelector' is used to select 
         -- rules from a problem. Various combinators 
         -- are implemented.
       , RuleSelector (..)
       , RuleSetSelector
       , ExpressionSelector
         
       -- * Primitives
       , selRules
       , selDPs
       , selStricts
       , selWeaks
         -- * Constructors
       , selFromWDG
       , selFromCWDG
         -- * Combinators
       , selInverse
       , selCombine
       , selUnion
       , selInter
         -- * Rule-selectors based on dependency graphs
       , selFirstCongruence
       , selFirstStrictCongruence
         -- * Boolean Selectors
       , selAnyOf
       , selAllOf
       , selAnd
       , selOr
        -- * Misc
       , selAnyLeaf
       , selStrictLeafs
       , selFirstAlternative         
       , rules
       , onSelectedRequire
       ) where

import Data.Typeable (Typeable)
import Data.List (intersperse)
import Tct.Processor (SelectorExpression(..))
import Tct.Method.DP.DependencyGraph
import Qlogic.Boolean (bigAnd, bigOr, Boolean)
import Data.Graph.Inductive.Query.BFS (bfsn)
import qualified Tct.Method.DP.DependencyGraph as DG
import Tct.Processor.Args.Instances
import qualified Termlib.Problem as Prob
import qualified Termlib.Trs as Trs
import Termlib.Rule (Rule)
import Termlib.Problem (Problem)

-- | This datatype is used to select a subset of rules recorded in a problem.
data RuleSelector a = RuleSelector { rsName :: String -- ^ Name of the rule selector.
                                   , rsSelect :: Problem -> a -- ^ Given a problem, computes an 'SelectorExpression' that 
                                                            -- determines which rules to selct.
                         } deriving Typeable

type RuleSetSelector = RuleSelector Prob.Ruleset
type ExpressionSelector = RuleSelector SelectorExpression

instance Show (RuleSelector a) where show = rsName

instance AssocArgument (RuleSelector SelectorExpression) where 
    assoc _ = [ ("any " ++ n, selAnyOf s) | (n,s) <- prims ]
              ++ [ ("all " ++ n, selAllOf s) | (n,s) <- prims ]
      where prims = [ ("all", selDPs `selUnion` selRules)
                    , ("dps", selDPs)
                    , ("rules", selRules)
                    , ("stricts", selStricts)
                    , ("weaks", selWeaks)
                    , ("first congruence", selFirstCongruence)                       
                    , ("first strict congruence", selFirstStrictCongruence)]

          
-- | Inverses the selection.
selInverse :: RuleSetSelector -> RuleSetSelector
selInverse s = RuleSelector { rsName = "inverse of " ++ rsName s
                            , rsSelect = fn }
    where fn prob = Prob.Ruleset { Prob.sdp  = inv Prob.strictDPs Prob.sdp
                                 , Prob.wdp  = inv Prob.weakDPs Prob.wdp
                                 , Prob.strs = inv Prob.strictTrs Prob.strs
                                 , Prob.wtrs = inv Prob.weakTrs Prob.wtrs }
            where rs = rsSelect s prob
                  inv pfn rfn = pfn prob Trs.\\ rfn rs

-- | Combine two rule-selectors component-wise.
selCombine :: (String -> String -> String) -> (Trs.Trs -> Trs.Trs -> Trs.Trs) -> (RuleSetSelector -> RuleSetSelector -> RuleSetSelector)
selCombine cn ctrs s1 s2 = RuleSelector { rsName = cn (rsName s1) (rsName s2)
                                        , rsSelect = fn }
        where fn prob = Prob.Ruleset { Prob.sdp  = un Prob.sdp
                                     , Prob.wdp  = un Prob.wdp
                                     , Prob.strs = un Prob.strs
                                     , Prob.wtrs = un Prob.wtrs }
                where rs1 = rsSelect s1 prob
                      rs2 = rsSelect s2 prob
                      un rfn = rfn rs1 `ctrs` rfn rs2

-- | Select union of selections of given rule-selectors.
selUnion :: RuleSetSelector -> RuleSetSelector -> RuleSetSelector
selUnion = selCombine (\ n1 n2 -> "union of " ++ n1 ++ " and " ++ n2) Trs.union

-- | Select intersection of selections of given rule-selectors.
selInter :: RuleSetSelector -> RuleSetSelector -> RuleSetSelector
selInter= selCombine (\ n1 n2 -> "intersect of " ++ n1 ++ " and " ++ n2) Trs.intersect

-- | Select rewrite rules, i.e., non dependency pair rules.
selRules :: RuleSetSelector
selRules = RuleSelector { rsName   = "rewrite-rules" , rsSelect = fn } 
    where fn prob = Prob.Ruleset { Prob.sdp = Trs.empty
                                 , Prob.wdp = Trs.empty
                                 , Prob.strs = Prob.strictTrs prob
                                 , Prob.wtrs = Prob.weakTrs prob }
           
-- | Select dependency pairs.
selDPs :: RuleSetSelector
selDPs = RuleSelector { rsName = "DPs" , rsSelect = fn }
    where fn prob = Prob.Ruleset { Prob.sdp = Prob.strictDPs prob
                                 , Prob.wdp = Prob.weakDPs prob
                                 , Prob.strs = Trs.empty
                                 , Prob.wtrs = Trs.empty }

-- | Select strict rules.
selStricts :: RuleSetSelector
selStricts = RuleSelector { rsName = "strict-rules" , rsSelect = fn }
    where fn prob = Prob.Ruleset { Prob.sdp = Prob.strictDPs prob
                                 , Prob.wdp = Trs.empty
                                 , Prob.strs = Prob.strictTrs prob
                                 , Prob.wtrs = Trs.empty }

-- | Select strict rules.
selWeaks :: RuleSetSelector
selWeaks = RuleSelector { rsName = "weak-rules" , rsSelect = fn }
    where fn prob = Prob.Ruleset { Prob.sdp = Trs.empty
                                 , Prob.wdp = Prob.weakDPs prob
                                 , Prob.strs = Trs.empty
                                 , Prob.wtrs = Prob.weakTrs prob }

-- | Select from the dependency graph, using the given function. 
-- The first parameter should specify a short name for the rule-selector.
selFromWDG :: String -> (DG -> Prob.Ruleset) -> RuleSetSelector
selFromWDG n f = RuleSelector { rsName = n
                              , rsSelect = \ prob -> f (dg prob) }
    where dg = DG.estimatedDependencyGraph DG.defaultApproximation

-- | Select from the congruence dependency graph, using the given function.
-- The first parameter should specify a short name for the rule-selector.          
selFromCWDG :: String -> (CDG -> Prob.Ruleset) -> RuleSetSelector
selFromCWDG n f = RuleSelector { rsName = n
                               , rsSelect = \ prob -> f (dg prob) }
    where dg = toCongruenceGraph . DG.estimatedDependencyGraph DG.defaultApproximation

restrictToCongruences :: Prob.Ruleset -> [NodeId] -> CDG -> Prob.Ruleset
restrictToCongruences rs ns cdg = rs { Prob.sdp = Trs.fromRules [ r | (DG.StrictDP, r) <- rr]
                                     , Prob.wdp = Trs.fromRules [ r | (DG.WeakDP, r) <- rr] }
    where rr = allRulesFromNodes cdg ns

-- | Selects all rules from root-nodes in the congruence graph.
selFirstCongruence :: RuleSetSelector
selFirstCongruence = selFromCWDG "first congruence from CWDG" fn
    where fn cdg = restrictToCongruences Prob.emptyRuleset (roots cdg) cdg 

-- | Selects all rules from nodes @n@ of the CWDG that satisfy
-- (i) the node @n@ references at least one strict rule, and (ii)
-- there is no node between a root of the CWDG and @n@ containing a strict rule.
selFirstStrictCongruence :: RuleSetSelector
selFirstStrictCongruence = selFromCWDG "first congruence with strict rules from CWDG" fn
    where fn cdg = restrictToCongruences Prob.emptyRuleset ns cdg 
              where ns = take 1 $ [ n | n <- bfsn (roots cdg) cdg
                                  , any ((==) DG.StrictDP . fst) (allRulesFromNodes cdg [n])  ]

selAnyLeaf :: ExpressionSelector
selAnyLeaf = selAnyOf $ selFromCWDG "strict leaf in CWDG" sel
  where sel cwdg = Prob.emptyRuleset { Prob.sdp = Trs.fromRules [ r | (DG.StrictDP, r) <- leafRules cwdg] }
        leafRules cwdg = DG.allRulesFromNodes cwdg (DG.leafs cwdg)

selStrictLeafs :: ExpressionSelector
selStrictLeafs = selAllOf $ selFromWDG "all leaf rules from WDG" sel
          where sel wdg = Prob.emptyRuleset { Prob.sdp = Trs.fromRules rs }
                  where stricts = [ (n,r) | (n,(DG.StrictDP,r)) <- DG.withNodeLabels' wdg (DG.nodes wdg)]
                        rs = [ r | (n, r) <- stricts
                                 , all (\ (m, (strictness, _)) -> n == m || strictness == DG.WeakDP) $ DG.withNodeLabels' wdg $ DG.reachablesDfs wdg [n] ]

selAnyOf :: RuleSetSelector -> ExpressionSelector
selAnyOf s = RuleSelector { rsName = "any " ++ rsName s
                          , rsSelect = f }
  where f prob = BigOr $ [ SelectDP d | d <- Trs.rules $ Prob.sdp rs `Trs.union` Prob.wdp rs]
                         ++ [ SelectTrs r | r <- Trs.rules $ Prob.strs rs `Trs.union` Prob.wtrs rs]
          where rs = rsSelect s prob

selAllOf :: RuleSetSelector -> ExpressionSelector
selAllOf s = RuleSelector { rsName = "any " ++ rsName s
                          , rsSelect = f }
  where f prob = BigAnd $ [ SelectDP d | d <- Trs.rules $ Prob.sdp rs `Trs.union` Prob.wdp rs]
                         ++ [ SelectTrs r | r <- Trs.rules $ Prob.strs rs `Trs.union` Prob.wtrs rs]
          where rs = rsSelect s prob


-- | Conjunction
selAnd :: [ExpressionSelector] -> ExpressionSelector
selAnd ss = RuleSelector { rsName = "all [" ++ concat (intersperse ", " [rsName s | s <- ss])  ++ "]"
                         , rsSelect = \ prob -> BigAnd [rsSelect s prob | s <- ss] }

-- | Disjunction
selOr :: [ExpressionSelector] -> ExpressionSelector
selOr ss = RuleSelector { rsName = "any [" ++ concat (intersperse ", " [rsName s | s <- ss])  ++ "]"
                        , rsSelect = \ prob -> BigOr [rsSelect s prob | s <- ss] }


-- | Selects the first alternative from the given rule selector.
selFirstAlternative :: ExpressionSelector -> ExpressionSelector
selFirstAlternative rs = RuleSelector { rsName = "first alternative of " ++ rsName rs , 
                                        rsSelect = \ prob -> let (dps, trs) = selectFirst $ rsSelect rs prob
                                                             in BigAnd $ [SelectDP d | d <- Trs.rules dps]
                                                                ++ [SelectTrs r | r <- Trs.rules trs]
                                      }
  where selectFirst (BigAnd ss)   = (Trs.unions dpss, Trs.unions trss)
          where (dpss, trss) = unzip [selectFirst sel | sel <- ss]
        selectFirst (BigOr [])      = (Trs.empty,Trs.empty)
        selectFirst (BigOr (sel:_)) = selectFirst sel
        selectFirst (SelectDP d)    = (Trs.singleton d, Trs.empty)
        selectFirst (SelectTrs r)   = (Trs.empty, Trs.singleton r)
        
-- | returns the pair of dps and rules mentioned in a 'SelectorExpression'        
rules :: SelectorExpression -> (Trs.Trs, Trs.Trs)
rules e =  
  case e of 
    BigAnd ss -> rules' ss
    BigOr ss -> rules' ss    
    SelectDP d -> (Trs.singleton d, Trs.empty)
    SelectTrs r -> (Trs.empty, Trs.singleton r)
  where rules' ss = (Trs.unions dpss, Trs.unions trss)
          where (dpss, trss) = unzip [rules sel | sel <- ss] 


onSelectedRequire :: Boolean a => SelectorExpression -> (Bool -> Rule -> a) -> a
onSelectedRequire (SelectDP r) f = f True r
onSelectedRequire (SelectTrs r) f = f False r
onSelectedRequire (BigAnd es) f = bigAnd [ onSelectedRequire e f | e <- es]
onSelectedRequire (BigOr es) f = bigOr [ onSelectedRequire e f | e <- es]          
