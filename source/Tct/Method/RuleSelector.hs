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
         -- | A 'RuleSelector' is used to select 
         -- rules from a problem. Various combinators 
         -- are implemented.
       RuleSelector (..)
       , selRules
       , selDPs
       , selStricts
       , selWeaks
       , selAnyOf
       , selAllOf
       , selectFirstAlternative         
         -- * Rule-selectors based on dependency graphs
       , selFromWDG
       , selFromCWDG
       , selFirstCongruence
       , selFirstStrictCongruence
       , selAnyWDGLeafs         
       , selAnyCWDGLeafs
         -- * Combinators
       , selNeg
       , selAnd
       , selOr
        -- * Misc
       , rules
       ) where

import Data.Typeable (Typeable)
import Data.List (intersperse, partition)
import Tct.Processor (SelectorExpression(..))
import Tct.Method.DP.DependencyGraph
import Data.Graph.Inductive.Query.BFS (bfsn)
import qualified Tct.Method.DP.DependencyGraph as DG
import Tct.Processor.Args.Instances
import qualified Termlib.Problem as Prob
import qualified Termlib.Trs as Trs
import Termlib.Problem (Problem)

-- | This datatype is used to select a subset of rules recorded in a problem.
data RuleSelector a = RS { rsName :: String -- ^ Name of the rule selector.
                         , rsSelect :: a -> Problem -> SelectorExpression -- ^ Given state 'a' and problem, computes an 'SelectorExpression' that 
                                                                       -- ^ determines which rules to selct.
                         } deriving Typeable

instance Show (RuleSelector a) where show = rsName

instance AssocArgument (RuleSelector ()) where 
    assoc _ = [ ("all", selAnd [selDPs, selRules])
              , ("dps", selDPs)
              , ("rules", selRules)
              , ("stricts", selStricts)
              , ("weaks", selWeaks)
              , ("first congruence", selFirstCongruence)                       
              , ("first strict congruence", selFirstStrictCongruence)]



-- | Negation. 
selNeg :: RuleSelector a -> RuleSelector a
selNeg s = RS { rsName = "inverse of " ++ rsName s
              , rsSelect = \ a prob -> inv prob $ rsSelect s a prob }
    where inv prob (SelectDP rs)  = SelectDP $ Prob.dpComponents prob Trs.\\ rs
          inv prob (SelectTrs rs) = SelectTrs $ Prob.trsComponents prob Trs.\\ rs          
          inv prob (BigAnd es)    = BigOr [ inv prob e | e <- es]
          inv prob (BigOr es)     = BigAnd [ inv prob e | e <- es]          
          

-- | Conjunction
selAnd :: [RuleSelector a] -> RuleSelector a
selAnd ss = RS { rsName = "all [" ++ concat (intersperse ", " [rsName s | s <- ss])  ++ "]"
               , rsSelect = \ a prob -> BigAnd [rsSelect s a prob | s <- ss] }

-- | Disjunction
selOr :: [RuleSelector a] -> RuleSelector a
selOr ss = RS { rsName = "any [" ++ concat (intersperse ", " [rsName s | s <- ss])  ++ "]"
              , rsSelect = \ a prob -> BigOr [rsSelect s a prob | s <- ss] }

-- | Select dependency pairs.
selDPs :: RuleSelector a
selDPs = RS { rsName = "DPs" 
            , rsSelect = \ _ prob -> SelectDP (Prob.dpComponents prob) }

selAnyOf :: String -> Trs.Trs -> RuleSelector a
selAnyOf n trs = RS { rsName = n , rsSelect = sel }
 where sel _ prob = BigOr [ singl r | r <- Trs.rules trs]
         where singl r | Trs.member dps r = SelectDP $ Trs.singleton r
                       | otherwise        = SelectTrs $ Trs.singleton r
               dps = Prob.dpComponents prob

selAllOf :: String -> Trs.Trs -> RuleSelector a
selAllOf n trs = RS { rsName = n , rsSelect = sel }
 where sel _ prob = BigAnd [ SelectDP (Trs.fromRules dps')
                           , SelectTrs (Trs.fromRules trs')]
         where (dps',trs') = partition (Trs.member dps) $ Trs.rules trs
               dps = Prob.dpComponents prob


-- | Select rewrite rules.
selRules :: RuleSelector a
selRules = RS { rsName = "TRS" , rsSelect = \ _ prob -> SelectDP (Prob.trsComponents prob) }

-- | Select strict rules.
selStricts :: RuleSelector a
selStricts = RS { rsName = "strict" , rsSelect = \ _ prob -> SelectDP (Prob.strictComponents prob) }

-- | Select weak rules.
selWeaks :: RuleSelector a
selWeaks = RS { rsName = "weak" , rsSelect = \ _ prob -> SelectDP (Prob.weakComponents prob) }

-- | Selects the first alternative from the given rule selector.
selectFirstAlternative :: RuleSelector a -> RuleSelector a
selectFirstAlternative rs = RS { rsName = "first alternative of " ++ rsName rs , 
                                 rsSelect = \ a prob -> let (dps, trs) = selectFirst $ rsSelect rs a prob
                                                        in BigAnd [SelectDP dps, SelectTrs trs]
                               }
  where selectFirst (BigAnd ss)   = (intersects dpss, intersects trss)
          where (dpss, trss) = unzip [selectFirst sel | sel <- ss]
                intersects [] = Trs.empty
                intersects (t:ts) = foldl Trs.intersect t ts
        selectFirst (BigOr [])    = (Trs.empty,Trs.empty)
        selectFirst (BigOr (sel:_)) = selectFirst sel
        selectFirst (SelectDP dps) = (dps, Trs.empty)
        selectFirst (SelectTrs trs) = (Trs.empty, trs)
        
        
-- | returns the pair of dps and rules mentioned in a 'SelectorExpression'        
rules :: SelectorExpression -> (Trs.Trs, Trs.Trs)
rules e =  
  case e of 
    BigAnd ss -> rules' ss
    BigOr ss -> rules' ss    
    SelectDP dps -> (dps, Trs.empty)
    SelectTrs trs -> (Trs.empty, trs)
  where rules' ss = (Trs.unions dpss, Trs.unions trss)
          where (dpss, trss) = unzip [rules sel | sel <- ss] 

-- | Select from the dependency graph, using the given function. 
-- The first parameter should specify a short name for the rule-selector.
selFromWDG :: String -> (a -> DG -> SelectorExpression) -> RuleSelector a
selFromWDG n f = RS { rsName = n
                    , rsSelect = \a prob -> f a (dg prob) }
    where dg = estimatedDependencyGraph Edg

-- | Select from the congruence dependency graph, using the given function.
-- The first parameter should specify a short name for the rule-selector.          
selFromCWDG :: String -> (a -> CDG -> SelectorExpression) -> RuleSelector a
selFromCWDG n f = RS { rsName = n
                     , rsSelect = \a prob -> f a (dg prob) }
    where dg = toCongruenceGraph . estimatedDependencyGraph Edg

selFromCongruences :: [NodeId] -> CDG -> SelectorExpression
selFromCongruences ns cdg = SelectDP $ Trs.fromRules $ [ r | (_, r) <- allRulesFromNodes cdg ns]

-- | Selects all rules from root-nodes in the congruence graph.
selFirstCongruence :: RuleSelector a
selFirstCongruence = selFromCWDG "first congruence from CWDG" fn
    where fn _ cdg = selFromCongruences (roots cdg) cdg 

-- | Selects all rules from nodes @n@ of the CWDG that satisfy
-- (i) the node @n@ references at least one strict rule, and (ii)
-- there is no node between a root of the CWDG and @n@ containing a strict rule.
selFirstStrictCongruence :: RuleSelector a
selFirstStrictCongruence = selFromCWDG "first congruence with strict rules from CWDG" fn
    where fn _ cdg = selFromCongruences ns cdg 
              where ns = take 1 $ [ n | n <- bfsn (roots cdg) cdg
                                  , any ((==) DG.StrictDP . fst) (allRulesFromNodes cdg [n])  ]

selAnyWDGLeafs :: RuleSelector a
selAnyWDGLeafs = selFromWDG "any leaf rule from WDG" sel
  where sel _ wdg = BigOr [ SelectDP (Trs.singleton r) 
                          | (_,(_,r)) <- DG.withNodeLabels' wdg (DG.leafs wdg)]

selAnyCWDGLeafs :: RuleSelector a
selAnyCWDGLeafs = selFromCWDG "any leaf rule from CWDG" sel
  where sel _ wdg = BigOr [ SelectDP (Trs.singleton r) 
                          | (_,r) <- DG.allRulesFromNodes wdg (DG.leafs wdg)]


