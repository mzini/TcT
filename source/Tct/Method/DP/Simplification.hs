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
import Text.PrettyPrint.HughesPJ hiding (empty)
import qualified Text.PrettyPrint.HughesPJ as PP


import qualified Termlib.FunctionSymbol as F
import qualified Termlib.Variable as V
import qualified Termlib.Problem as Prob
import qualified Termlib.Trs as Trs
import Termlib.Trs (Trs(..))
import qualified Termlib.Rule as Rule
import Termlib.Rule (Rule (..))
import qualified Termlib.Term as Term

import Termlib.Trs.PrettyPrint (pprintTrs)
import Termlib.Utils hiding (block)
import Data.Maybe (fromJust, isJust, fromMaybe)

import qualified Tct.Processor.Transformations as T
import qualified Tct.Processor as P
import Tct.Processor.Args
import Tct.Processor.PPrint
import Tct.Method.DP.Utils 
import Tct.Method.DP.DependencyGraph hiding (GroundContext)
import Tct.Method.DP.DependencyPairs
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
  pprintProof _ _ (Error e) = pprint e
  pprintProof _ _ p | null remls = text "No dependency-pair could be removed"
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
               where scc = fromJust $ lookupNode cwdg n
                                          

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
                  where initials = [ n | (n,cn) <- withNodes cwdg $ leafs cwdg
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
                                    
                    
              mkPairs n = theSCC $ lookupNode' cwdg n
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
                              , srhsSig           :: F.Signature
                              , srhsVars          :: V.Variables}                                
                  | SRHSError DPError
                       
instance T.TransformationProof SimpRHS where
  answer = T.answerFromSubProof
  pprintProof _ _ (SRHSError e) = pprint e
  pprintProof _ _ p | null repls = text "No rule was simplified"
                    | otherwise = text "The right-hand sides of following rules could be simplified:"
                                  $+$ text ""
                                  $+$ indent (pprint (Trs repls, sig, vars))
     where vars  = srhsVars p                              
           sig   = srhsSig p
           repls = srhsReplacedRules p

instance T.Transformer SimpRHS where 
  name _ = "simpDPRHS"
  type T.ArgumentsOf SimpRHS = Unit
  type T.ProofOf SimpRHS     = SimpRHSProof
  arguments _ = Unit
  transform _ prob | not (Trs.isEmpty strs) = return $ T.NoProgress $ SRHSError ContainsStrictRule
                   | progr            = return $ T.Progress proof (enumeration' [prob'])
                   | otherwise        = return $ T.NoProgress proof
    where proof = SRHSProof { srhsReplacedRules = [rule | (rule, Just _) <- elims]
                            , srhsSig           = Prob.signature prob
                            , srhsVars          = Prob.variables prob }
          strs  = Prob.strictTrs prob
          progr = any (isJust . snd) elims
          elims = [(rule, elim rule) | rule <- Trs.toRules $ Prob.strictDPs prob]
            where ds   = Trs.definedSymbols (Prob.dpComponents prob)
                  isDefinedWeak (Term.Fun f _) = Set.member f ds
                  isDefinedWeak _              = False
                  elim (Rule l (Term.Fun f rs)) | length rs == length rs' = Nothing
                                                | otherwise              = Just $ Rule l (Term.Fun f rs')
                        where rs' = filter isDefinedWeak rs
          prob' = withFreshCompounds prob { Prob.strictDPs = Trs.fromRules [ fromMaybe (fst p) (snd p) | p <- elims] }

simpDPRHSProcessor :: T.TransformationProcessor SimpRHS P.AnyProcessor
simpDPRHSProcessor = T.transformationProcessor SimpRHS

simpDPRHS :: T.TheTransformer SimpRHS
simpDPRHS = SimpRHS `T.calledWith` ()
