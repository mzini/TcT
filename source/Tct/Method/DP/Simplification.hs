--------------------------------------------------------------------------------
-- | 
-- Module      :  Tct.Method.DP.Simplification
-- Copyright   :  (c) Martin Avanzini <martin.avanzini@uibk.ac.at>, 
--                Georg Moser <georg.moser@uibk.ac.at>, 
--                Andreas Schnabl <andreas.schnabl@uibk.ac.at>,
-- License     :  LGPL (see COPYING)
--
-- Maintainer  :  Martin Avanzini <martin.avanzini@uibk.ac.at>
-- Stability   :  unstable
-- Portability :  unportable      
-- 
-- This module provides various fast transformations that simplify 
-- dependency pair problems.
--------------------------------------------------------------------------------   

{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleInstances #-}

module Tct.Method.DP.Simplification 
       (
         -- * Remove Tails
         removeTails
       , RemoveTailProof (..)
       , removeTailProcessor
       , RemoveTail
         
         -- * Simplify Dependency Pair Right-Hand-Sides
       , simpDPRHS
       , SimpRHSProof (..)
       , simpDPRHSProcessor
       , SimpRHS
         
         -- * Knowledge Propagation
       , simpKP
       , SimpKPProof (..)         
       , simpKPProcessor
       , SimpKP
       )
where

import qualified Data.Set as Set
import Data.List (partition)
import Text.PrettyPrint.HughesPJ hiding (empty)
import qualified Text.PrettyPrint.HughesPJ as PP


import qualified Termlib.FunctionSymbol as F
import qualified Termlib.Signature as Sig
import qualified Termlib.Variable as V
import qualified Termlib.Problem as Prob
import qualified Termlib.Trs as Trs
import Termlib.Trs (RuleList(..))
import Termlib.Rule (Rule (..))
import qualified Termlib.Term as Term

import Termlib.Trs.PrettyPrint (pprintTrs,pprintNamedTrs)
import Termlib.Utils hiding (block)
import Data.Maybe (isJust, fromMaybe, listToMaybe)

import qualified Tct.Processor.Transformations as T
import qualified Tct.Processor as P
import Tct.Processor.Args
import Tct.Utils.PPrint
import Tct.Utils.Enum (enumeration')
import Tct.Method.DP.Utils 
import Tct.Method.DP.DependencyGraph
import qualified Data.Graph.Inductive.Graph as Graph


data RemoveTail = RemoveTail
data RemoveTailProof = RLProof { removables :: [(NodeId, DGNode)] -- ^ Tail Nodes of the dependency graph.
                               , cgraph     :: CDG -- ^ Employed congruence graph.
                               , graph      :: DG -- ^ Employed weak dependency graph.
                               , signature  :: F.Signature
                               , variables  :: V.Variables}
                     | Error DPError
                       
instance T.TransformationProof RemoveTail where
  answer = T.answerFromSubProof
  pprintTProof _ _ (Error e) _ = pprint e
  pprintTProof _ _ p _ | null remls = text "No dependency-pair could be removed"
                       | otherwise  = 
     text "We consider the the dependency graph"
     $+$ text ""
     $+$ indent (pprintCWDG cwdg sig vars ppLabel)
     $+$ text ""
     $+$ paragraph "The following rules are either leafs or part of trailing weak paths, and thus they can be removed:"
     $+$ text ""
     $+$ indent (pprintTrs ppRule remls)
     where vars          = variables p                              
           sig           = signature p
           cwdg          = cgraph p
           wdg           = graph p
           remls         = removables p
           ppRule (i, (_,r)) = text (show i) <> text ":" <+> pprint (r, sig, vars)
           ppLabel _ n | onlyWeaks scc         = text "Weak SCC"
                       | nonSelfCyclic wdg scc = text "Noncyclic, trivial, SCC"
                       | otherwise             = PP.empty
               where scc = lookupNodeLabel' cwdg n
                                          

onlyWeaks :: CDGNode -> Bool
onlyWeaks = not . any ((==) StrictDP . fst . snd) . theSCC

nonSelfCyclic :: DG -> CDGNode -> Bool
nonSelfCyclic wdg sn = case theSCC sn of 
                         [(m,_)] -> not $ m `elem` successors wdg m 
                         _   -> False


instance T.Transformer RemoveTail where
  name RemoveTail        = "removetails"
  description RemoveTail = [unwords [ "Recursively removes all nodes that are either"
                                    , "leafs in the dependency-graph or from the given problem."
                                    , "Only applicable if the strict component is empty."]
                           ]
  
  type ArgumentsOf RemoveTail = Unit
  type ProofOf RemoveTail = RemoveTailProof
  arguments RemoveTail = Unit
  transform _ prob | not $ Trs.isEmpty $ Prob.strictTrs prob = return $ T.NoProgress $ Error $ ContainsStrictRule
                   | null labTails  = return $ T.NoProgress proof
                   | otherwise      = return $ T.Progress proof (enumeration' [prob'])
        where labTails = concatMap mkPairs $ Set.toList $ computeTails initials Set.empty
                  where initials = [ n | (n,cn) <- withNodeLabels' cwdg $ leafs cwdg
                                       , onlyWeaks cn || nonSelfCyclic wdg cn ]
              ls = map (snd . snd) labTails
              computeTails []             lfs = lfs
              computeTails (n:ns) lfs | n `Set.member` lfs = computeTails ns lfs
                                      | otherwise          = computeTails (ns++preds) lfs'
                   where (lpreds, _, cn, lsucs) = Graph.context cwdg n
                         sucs  = map snd lsucs
                         preds = map snd lpreds
                         lfs'  = if Set.fromList sucs `Set.isSubsetOf` lfs && (onlyWeaks cn || nonSelfCyclic wdg cn)
                                  then Set.insert n lfs 
                                  else lfs 
                                    
                    
              mkPairs n = theSCC $ lookupNodeLabel' cwdg n
              wdg   = estimatedDependencyGraph Edg prob
              cwdg  = toCongruenceGraph wdg
              sig   = Prob.signature prob
              vars  = Prob.variables prob
              proof = RLProof { removables = labTails
                              , graph      = wdg
                              , cgraph     = cwdg
                              , signature = sig
                              , variables = vars }
              prob' = prob { Prob.strictDPs = Prob.strictDPs prob Trs.\\ Trs ls
                           , Prob.weakDPs   = Prob.weakDPs prob Trs.\\ Trs ls }
                

removeTailProcessor :: T.Transformation RemoveTail P.AnyProcessor
removeTailProcessor = T.Transformation RemoveTail

-- | Removes trailing weak paths and and dangling rules. 
-- A dependency pair is on a trailing weak path if it is from the weak components and all sucessors in the dependency graph 
-- are on trailing weak paths. A rule is dangling if it has no successors in the dependency graph.
--  
-- Only applicable on DP-problems as obtained by 'dependencyPairs' or 'dependencyTuples'. Also 
-- not applicable when @strictTrs prob \= Trs.empty@.
removeTails :: T.TheTransformer RemoveTail
removeTails = T.Transformation RemoveTail `T.withArgs` ()



--------------------------------------------------------------------------------
--- Simplify DP-RHSs

data SimpRHS = SimpRHS
data SimpRHSProof = SRHSProof { srhsReplacedRules :: [Rule] -- ^ Rules that could be simplified.
                              , srhsDG            :: DG -- ^ Employed dependency graph.
                              , srhsSig           :: F.Signature
                              , srhsVars          :: V.Variables}                                
                  | SRHSError DPError
                       
instance T.TransformationProof SimpRHS where
  answer = T.answerFromSubProof
  pprintTProof _ _ (SRHSError e) _ = pprint e
  pprintTProof _ _ p _ | null repls = text "No rule was simplified"
                       | otherwise = 
       text "We consider the following dependency-graph" 
       $+$ text ""
       $+$ indent (pprint (dg, sig, vars))
       $+$ paragraph "Due to missing edges in the dependency-graph, the right-hand sides of following rules could be simplified:"
       $+$ text ""
       $+$ indent (pprint (Trs repls, sig, vars))
     where vars  = srhsVars p                              
           sig   = srhsSig p
           repls = srhsReplacedRules p
           dg    = srhsDG p

instance T.Transformer SimpRHS where 
  name _ = "simpDPRHS"
  type ArgumentsOf SimpRHS = Unit
  type ProofOf SimpRHS     = SimpRHSProof
  arguments _ = Unit
  description _ = [unwords [ "Simplify right hand sides of dependency pairs by removing marked subterms "
                           , "whose root symbols are undefined."
                           , "Only applicable if the strict component is empty."
                           ]
                  ]
  transform _ prob | not (Trs.isEmpty strs) = return $ T.NoProgress $ SRHSError ContainsStrictRule
                   | progr            = return $ T.Progress proof (enumeration' [prob'])
                   | otherwise        = return $ T.NoProgress proof
    where proof = SRHSProof { srhsReplacedRules = [rule | (_, _, rule, Just _) <- elims]
                            , srhsDG            = wdg
                            , srhsSig           = sig 
                            , srhsVars          = Prob.variables prob }
          strs  = Prob.strictTrs prob
          (c,sig) = Sig.runSignature (F.fresh (F.defaultAttribs "c" 0) { F.symIsCompound = True }) (Prob.signature prob)
          wdg   = estimatedDependencyGraph Edg prob
          progr = any (\ (_,_,_,mr) -> isJust mr) elims
          elims = [(n, s, rule, elim n rule) | (n,(s,rule)) <- lnodes wdg]
            where elim n (Rule l r@(Term.Fun f rs)) 
                      | F.isCompound sig f = elim' n l rs
                      | otherwise          = elim' n l [r]
                  elim n (Rule l r)        = elim' n l [r]
                  elim' n l rs | length rs == length rs' = Nothing
                               | otherwise              = Just $ Rule l (Term.Fun c rs')
                      where rs' = [ ri | (i,ri) <- zip [1..] rs
                                  , any (\ (_,_, j) -> i == j) succs ]
                            succs = lsuccessors wdg n
          prob' = Prob.withFreshCompounds prob { Prob.strictDPs = toTrs stricts
                                               , Prob.weakDPs   = toTrs weaks
                                               , Prob.signature = sig }
              where (stricts, weaks) = partition (\ (_, s, _, _) -> s == StrictDP) elims
                    toTrs l = Trs.fromRules [ fromMaybe r mr | (_,_,r,mr) <- l ]

simpDPRHSProcessor :: T.Transformation SimpRHS P.AnyProcessor
simpDPRHSProcessor = T.Transformation SimpRHS

-- | Simplifies right-hand sides of dependency pairs. 
-- Removes r_i from right-hand side @c_n(r_1,...,r_n)@ if no instance of 
-- r_i can be rewritten.
--  
-- Only applicable on DP-problems as obtained by 'dependencyPairs' or 'dependencyTuples'. Also 
-- not applicable when @strictTrs prob \= Trs.empty@.
simpDPRHS :: T.TheTransformer SimpRHS
simpDPRHS = T.Transformation SimpRHS `T.withArgs` ()


--------------------------------------------------------------------------------
--- Simplify DP-RHSs

data SimpKP = SimpKP
data SimpKPProof = SimpKPProof { skpDG            :: DG -- ^ Employed DependencyGraph
                               , skpRule          :: Maybe (NodeId,Rule) -- ^ Rule that can be moved into the weak component.
                               , skpPres          :: [Rule]  -- ^ All predecessors of rule which can be moved into weak component.
                               , skpSig           :: F.Signature
                               , skpVars          :: V.Variables}                                
                 | SimpKPErr DPError
                       
instance T.TransformationProof SimpKP where
  answer = T.answerFromSubProof
  pprintTProof _ _ (SimpKPErr e) _ = pprint e
  pprintTProof _ _ p _ = 
    case skpRule p of 
      Nothing -> text "No rule found for knowledge propagation"
      Just (i,rl) -> text "We consider the following dependency-graph" 
                    $+$ text ""
                    $+$ indent (pprint (dg, sig, vars))
                    $+$ text ""
                    $+$ paragraph "The number of applications of the rule"
                    $+$ text ""
                    $+$ indent (pprintNamedTrs sig vars rlname (Trs [rl]))
                    $+$ text ""                  
                    $+$ paragraph "is given by the number of applications of following rules"
                    $+$ text ""
                    $+$ indent (pprintNamedTrs sig vars prename (Trs (skpPres p)))
                    $+$ text ""
                    $+$ (text "We remove" <+> text rlname 
                         <+> text "from and add" <+> text prename 
                         <+> text "to the strict component.")
                      where vars  = skpVars p                              
                            sig   = skpSig p
                            dg    = skpDG p
                            rlname = "{" ++ show i ++ "}"
                            prename = "Pre(" ++ rlname ++ ")"

instance T.Transformer SimpKP where 
  name _ = "simpKP"
  type ArgumentsOf SimpKP = Unit
  type ProofOf SimpKP     = SimpKPProof
  arguments _ = Unit
  description SimpKP = [unwords [ "Moves a strict dependency into the weak component"
                                , "if all predecessors in the dependency graph are strict" 
                                , "and there is no edge from the rule to itself."
                                , "Only applicable if the strict component is empty."]
                       ]
  transform _ prob | not (Trs.isEmpty strs) = return $ T.NoProgress $ SimpKPErr ContainsStrictRule
                   | isJust mres          = return $ T.Progress proof (enumeration' [prob'])
                   | otherwise            = return $ T.NoProgress proof
    where wdg   = estimatedDependencyGraph Edg prob
          mres = listToMaybe [((n,rl),  [r | (_,(_,r),_) <- preds] ) 
                             | (n,(StrictDP, rl)) <- lnodes wdg
                             , let preds = lpredecessors wdg n
                             , all (\ (m,(strictness,_),_) -> m /= n && strictness == StrictDP) preds ]
          strs  = Prob.strictTrs prob
          sdps  = Prob.strictDPs prob
          wdps  = Prob.weakDPs prob
          proof = SimpKPProof { skpDG   = wdg
                              , skpRule = mrl
                              , skpPres = pres
                              , skpSig  = Prob.signature prob
                              , skpVars = Prob.variables prob}
          (mrl,pres) = maybe (Nothing,[]) (\ (nrl,rs) -> (Just nrl, rs)) mres
          prob' = maybe prob (\ (_,rl) -> prob { Prob.strictDPs = (Trs pres `Trs.union` sdps) Trs.\\ Trs [rl]
                                              , Prob.weakDPs   = (wdps Trs.\\ Trs pres) `Trs.union` Trs [rl]}) mrl

         

simpKPProcessor :: T.Transformation SimpKP P.AnyProcessor
simpKPProcessor = T.Transformation SimpKP

-- | Moves a strict dependency into the weak component
-- if all predecessors in the dependency graph are strict 
-- and there is no edge from the rule to itself.
-- Only applicable if the strict component is empty.
-- This processor is inspired by Knowledge Propagation used in AProVE, 
-- therefor its name.
simpKP :: T.TheTransformer SimpKP
simpKP = T.Transformation SimpKP `T.withArgs` ()
