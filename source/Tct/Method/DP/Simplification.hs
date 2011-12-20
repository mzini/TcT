{-
This file is part of the Tyrolean Complexity Tool (TCT).

The Tyrolean Complexity Tool is free software: you can redistribute it and/or modify
it under the terms of the GNU Lesser General Public License as published by
the Free Software Foundation, either version 3 of the License, or
(at your option) any later version.

The Tyrolean Complexity Tool is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU Lesser General Public License for more details.

You should have received a copy of the GNU Lesser General Public License
along with the Tyrolean Complexity Tool.  If not, see <http://www.gnu.org/licenses/>.
-}

{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleInstances #-}

module Tct.Method.DP.Simplification where

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
import Tct.Processor.PPrint
import Tct.Method.DP.Utils 
import Tct.Method.DP.DependencyGraph
import qualified Data.Graph.Inductive.Graph as Graph


data RemoveTail = RemoveTail
data RemoveTailProof = RLProof { removables :: [(NodeId, DGNode)] 
                               , cgraph     :: CDG
                               , graph      :: DG
                               , signature  :: F.Signature
                               , variables  :: V.Variables}
                     | Error DPError
                       
instance T.TransformationProof RemoveTail where
  answer = T.answerFromSubProof
  pprintTProof _ _ (Error e) = pprint e
  pprintTProof _ _ p | null remls = text "No dependency-pair could be removed"
                     | otherwise  = text "We consider the the dependency-graph"
                                    $+$ text ""
                                    $+$ indent (pprint (wdg, sig, vars))
                                    $+$ text ""
                                    $+$ text "together with the congruence-graph"
                                    $+$ text ""
                                    $+$ indent (pprintCWDG cwdg sig vars ppLabel)
                                    $+$ text ""
                                    $+$ text "The following rules are either leafs or part of trailing weak paths, and thus they can be removed:"
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
  description RemoveTail = ["Recursively removes all nodes that are either leafs in the dependency-graph or from the given problem"]
  
  type T.ArgumentsOf RemoveTail = Unit
  type T.ProofOf RemoveTail = RemoveTailProof
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
                

removeTailProcessor :: T.TransformationProcessor RemoveTail P.AnyProcessor
removeTailProcessor = T.transformationProcessor RemoveTail

removeTails :: T.TheTransformer RemoveTail
removeTails = RemoveTail `T.calledWith` ()



--------------------------------------------------------------------------------
--- Simplify DP-RHSs

data SimpRHS = SimpRHS
data SimpRHSProof = SRHSProof { srhsReplacedRules :: [Rule] 
                              , srhsDG            :: DG
                              , srhsSig           :: F.Signature
                              , srhsVars          :: V.Variables}                                
                  | SRHSError DPError
                       
instance T.TransformationProof SimpRHS where
  answer = T.answerFromSubProof
  pprintTProof _ _ (SRHSError e) = pprint e
  pprintTProof _ _ p | null repls = text "No rule was simplified"
                     | otherwise = text "We consider the following dependency-graph" 
                                   $+$ text ""
                                   $+$ indent (pprint (dg, sig, vars))
 
                                   $+$ text "Due to missing edges in the dependency-graph, the right-hand sides of following rules could be simplified:"
                                   $+$ text ""
                                   $+$ indent (pprint (Trs repls, sig, vars))
     where vars  = srhsVars p                              
           sig   = srhsSig p
           repls = srhsReplacedRules p
           dg    = srhsDG p

instance T.Transformer SimpRHS where 
  name _ = "simpDPRHS"
  type T.ArgumentsOf SimpRHS = Unit
  type T.ProofOf SimpRHS     = SimpRHSProof
  arguments _ = Unit
  transform _ prob | not (Trs.isEmpty strs) = return $ T.NoProgress $ SRHSError ContainsStrictRule
                   | progr            = return $ T.Progress proof (enumeration' [prob'])
                   | otherwise        = return $ T.NoProgress proof
    where proof = SRHSProof { srhsReplacedRules = [rule | (_, _, rule, Just _) <- elims]
                            , srhsDG            = wdg
                            , srhsSig           = Prob.signature prob'
                            , srhsVars          = Prob.variables prob' }
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

simpDPRHSProcessor :: T.TransformationProcessor SimpRHS P.AnyProcessor
simpDPRHSProcessor = T.transformationProcessor SimpRHS

simpDPRHS :: T.TheTransformer SimpRHS
simpDPRHS = SimpRHS `T.calledWith` ()


--------------------------------------------------------------------------------
--- Simplify DP-RHSs

data SimpKP = SimpKP
data SimpKPProof = SimpKPProof { skpDG            :: DG
                               , skpRule          :: Maybe (Int,Rule)
                               , skpPres          :: [Rule]
                               , skpSig           :: F.Signature
                               , skpVars          :: V.Variables}                                
                 | SimpKPErr DPError
                       
instance T.TransformationProof SimpKP where
  answer = T.answerFromSubProof
  pprintTProof _ _ (SimpKPErr e) = pprint e
  pprintTProof _ _ p = 
    case skpRule p of 
      Nothing -> text "No rule found for knowledge propagation"
      Just (i,rl) -> text "We consider the following dependency-graph" 
                    $+$ text ""
                    $+$ indent (pprint (dg, sig, vars))
                    $+$ text ""
                    $+$ text "The number of applications of the rule"
                    $+$ text ""
                    $+$ indent (pprintNamedTrs sig vars rlname (Trs [rl]))
                    $+$ text ""                  
                    $+$ text "is given by the number of applications of following rules"
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
  type T.ArgumentsOf SimpKP = Unit
  type T.ProofOf SimpKP     = SimpKPProof
  arguments _ = Unit
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
                              , skpVars  = Prob.variables prob}
          (mrl,pres) = maybe (Nothing,[]) (\ (nrl,rs) -> (Just nrl, rs)) mres
          prob' = maybe prob (\ (_,rl) -> prob { Prob.strictDPs = (Trs pres `Trs.union` sdps) Trs.\\ Trs [rl]
                                              , Prob.weakDPs   = (wdps Trs.\\ Trs pres) `Trs.union` Trs [rl]}) mrl

         

simpKPProcessor :: T.TransformationProcessor SimpKP P.AnyProcessor
simpKPProcessor = T.transformationProcessor SimpKP

simpKP :: T.TheTransformer SimpKP
simpKP = SimpKP `T.calledWith` ()
