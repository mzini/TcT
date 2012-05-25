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
         
         -- * Trivial DP Problems
       , trivial
       , TrivialProof (..)
       , trivialProcessor
       , Trivial
         
         
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
import Data.List (sortBy)

import qualified Tct.Certificate as Cert
import qualified Tct.Processor.Transformations as T
import qualified Tct.Processor as P
import Tct.Processor.Args
import Tct.Utils.PPrint
import Tct.Utils.Enum (enumeration')
import Tct.Method.DP.Utils 
import Tct.Method.DP.DependencyGraph hiding (Trivial)
import qualified Data.Graph.Inductive.Graph as Graph


----------------------------------------------------------------------
-- Remove Tail

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
     $+$ paragraph "The following rules are part of trailing weak paths, and thus they can be removed:"
     $+$ text ""
     $+$ indent (pprintTrs ppRule remls)
     where vars          = variables p                              
           sig           = signature p
           cwdg          = cgraph p
           remls         = removables p
           ppRule (i, (_,r)) = text (show i) <> text ":" <+> pprint (r, sig, vars)
           ppLabel _ n | onlyWeaks scc         = text "Weak SCC"
                       | otherwise             = PP.empty
               where scc = lookupNodeLabel' cwdg n
                                          

onlyWeaks :: CDGNode -> Bool
onlyWeaks = not . any ((==) StrictDP . fst . snd) . theSCC

instance T.Transformer RemoveTail where
  name RemoveTail        = "removetails"
  description RemoveTail = [unwords [ "Removes trailing paths that do not need to be oriented."
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
                                       , onlyWeaks cn ]
              ls = map (snd . snd) labTails
              computeTails []             lfs = lfs
              computeTails (n:ns) lfs | n `Set.member` lfs = computeTails ns lfs
                                      | otherwise          = computeTails (ns++preds) lfs'
                   where (lpreds, _, cn, lsucs) = Graph.context cwdg n
                         sucs  = map snd lsucs
                         preds = map snd lpreds
                         lfs'  = if Set.fromList sucs `Set.isSubsetOf` lfs && (onlyWeaks cn)
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

-- | Removes trailing weak paths. 
-- A dependency pair is on a trailing weak path if it is from the weak components and all sucessors in the dependency graph 
-- are on trailing weak paths.
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
          mres = listToMaybe $ sortBy strictOutDeg candidates
          candidates = [ ((n,rl),  [r | (_,(_,r),_) <- preds] ) 
                       | (n,(StrictDP, rl)) <- lnodes wdg
                       , let preds = lpredecessors wdg n
                       , all (\ (m,(strictness,_),_) -> m /= n && strictness == StrictDP) preds ]
          ((n1, _), _) `strictOutDeg` ((n2, _), _) = length (strictSuccessors n1) `compare` length (strictSuccessors n2)
                       where strictSuccessors n = [ n' | (n', (StrictDP,_),_) <- lsuccessors wdg n ]
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


----------------------------------------------------------------------
-- Remove Tail

data Trivial = Trivial
data TrivialProof = TrivialProof { trivialCDG   :: CDG -- ^ Employed congruence graph.
                                 , trivialSig   :: F.Signature
                                 , trivialVars  :: V.Variables}
                  | TrivialError DPError
                  | TrivialFail
                       
instance T.TransformationProof Trivial where
  answer _ = P.CertAnswer $ Cert.certified (Cert.constant, Cert.constant)
  pprintTProof _ _ (TrivialError e) _ = pprint e
  pprintTProof _ _ TrivialFail _ = text "The DP problem is not trivial."
  pprintTProof _ _ p _ = 
     text "We consider the the dependency graph"
     $+$ text ""
     $+$ indent (pprintCWDG cwdg sig vars ppLabel)
     $+$ text ""
     $+$ paragraph "All SCCs are trivial."
     where vars          = trivialVars p                              
           sig           = trivialSig p
           cwdg          = trivialCDG p
           ppLabel _ _ = text "trivial"

instance T.Transformer Trivial where
  name Trivial        = "trivial"
  description Trivial = [unwords [ "Checks wether the DP problem is trivial, i.e. the dependency graph contains no loops."
                                 , "Only applicable if the strict component is empty."]
                        ]
  
  type ArgumentsOf Trivial = Unit
  type ProofOf Trivial = TrivialProof
  arguments Trivial = Unit
  transform _ prob | not $ Trs.isEmpty $ Prob.strictTrs prob = return $ T.NoProgress $ TrivialError $ ContainsStrictRule
                   | cyclic    = return $ T.NoProgress proof
                   | otherwise = return $ T.Progress proof (enumeration' [])
        where cyclic = any (isCyclicNode cwdg) (nodes cwdg)
              wdg   = estimatedDependencyGraph Edg prob
              cwdg  = toCongruenceGraph wdg
              sig   = Prob.signature prob
              vars  = Prob.variables prob
              proof = TrivialProof { trivialCDG = cwdg
                                   , trivialSig = sig
                                   , trivialVars = vars }
                

trivialProcessor :: T.Transformation Trivial P.AnyProcessor
trivialProcessor = T.Transformation Trivial

-- | Checks whether the DP problem is trivial, i.e., does not contain any cycles.
--  
-- Only applicable on DP-problems as obtained by 'dependencyPairs' or 'dependencyTuples'. Also 
-- not applicable when @strictTrs prob \= Trs.empty@.
trivial :: T.TheTransformer Trivial
trivial = T.Transformation Trivial `T.withArgs` ()
