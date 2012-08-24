{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeOperators #-}
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
         
         -- * Removing of InapplicableRules
       , removeInapplicable
       , RemoveInapplicableProof (..)
       , removeInapplicableProcessor
       , RemoveInapplicable

         
         -- * Knowledge Propagation
       , simpKP
       , simpKPOn
       , withKPOn
       , SimpKPProof (..)         
       , simpKPProcessor
       , SimpKP
       )
where

import qualified Data.Set as Set
import Data.List (partition, find)
import Data.Maybe (catMaybes)
import Text.PrettyPrint.HughesPJ hiding (empty)
import qualified Text.PrettyPrint.HughesPJ as PP

import qualified Termlib.FunctionSymbol as F
import qualified Termlib.Signature as Sig
import qualified Termlib.Variable as V
import qualified Termlib.Problem as Prob
import qualified Termlib.Trs as Trs
import Termlib.Rule (Rule (..))
import qualified Termlib.Term as Term
import Termlib.Term (properSubterms, functionSymbols)

import Termlib.Trs.PrettyPrint (pprintNamedTrs, pprintTrs)
import Termlib.Utils hiding (block)
import Data.Maybe (isJust, fromMaybe)

import qualified Tct.Certificate as Cert
import qualified Tct.Processor.Transformations as T
import qualified Tct.Processor as P
import Tct.Processor.Args as A
import Tct.Processor.Args.Instances
import Tct.Utils.PPrint
import Tct.Utils.Enum (enumeration')
import Tct.Method.DP.Utils 
import Tct.Method.DP.DependencyGraph hiding (Trivial)
import Tct.Method.RuleSelector as RS

import qualified Data.Graph.Inductive.Graph as Graph


----------------------------------------------------------------------
-- Remove Tail

data RemoveTail = RemoveTail
data RemoveTailProof = RTProof { removables :: [(NodeId, DGNode)] -- ^ Tail Nodes of the dependency graph.
                               , cgraph     :: CDG -- ^ Employed congruence graph.
                               , graph      :: DG -- ^ Employed weak dependency graph.
                               , signature  :: F.Signature
                               , variables  :: V.Variables}
                     | RTError DPError
                       
instance T.TransformationProof RemoveTail where
  answer = T.answerFromSubProof
  pprintTProof _ _ (RTError e) _ = pprint e
  pprintTProof _ _ p _ | null remls = text "No weak dependency pair could be removed."
                       | otherwise  = 
     text "We consider the (approximated) congruence graph"
     $+$ text ""
     $+$ indent (pprintCWDG cwdg sig vars ppLabel)
     $+$ text ""
     $+$ paragraph "and the following set of dependency pairs."
     $+$ text ""
     $+$ indent (pprintTrs ppRule remls)
     $+$ text ""
     $+$ paragraph ("The problem can be simplified by removing these pairs, "
                    ++ "as they only occur in suffixes of paths through the dependency graph.")
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
  transform _ prob 
     | not $ Trs.isEmpty $ Prob.strictTrs prob = return $ T.NoProgress $ RTError $ ContainsStrictRule
     | not $ Prob.isDPProblem prob = return $ T.NoProgress $ RTError $ NonDPProblemGiven
     | null labTails  = return $ T.NoProgress proof
     | otherwise      = return $ T.Progress proof (enumeration' [prob'])
        where labTails = concatMap mkPairs $ Set.toList $ computeTails initials Set.empty
                  where initials = [ n | (n,cn) <- withNodeLabels' cwdg $ leafs cwdg
                                       , onlyWeaks cn ]
              ls = Trs.fromRules $ map (snd . snd) labTails
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
              wdg   = estimatedDependencyGraph defaultApproximation prob
              cwdg  = toCongruenceGraph wdg
              sig   = Prob.signature prob
              vars  = Prob.variables prob
              proof = RTProof { removables = labTails
                              , graph      = wdg
                              , cgraph     = cwdg
                              , signature = sig
                              , variables = vars }
              prob' = prob { Prob.strictDPs = Prob.strictDPs prob Trs.\\ ls
                           , Prob.weakDPs   = Prob.weakDPs prob Trs.\\ ls }
                

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
       $+$ indent (pprint (Trs.fromRules repls, sig, vars))
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
  transform _ prob 
     | not (Trs.isEmpty strs)      = return $ T.NoProgress $ SRHSError ContainsStrictRule
     | not $ Prob.isDPProblem prob = return $ T.NoProgress $ SRHSError $ NonDPProblemGiven
     | progr                     = return $ T.Progress proof (enumeration' [prob'])
     | otherwise                 = return $ T.NoProgress proof
    where proof = SRHSProof { srhsReplacedRules = [rule | (_, _, rule, Just _) <- elims]
                            , srhsDG            = wdg
                            , srhsSig           = sig 
                            , srhsVars          = Prob.variables prob }
          strs  = Prob.strictTrs prob
          (c,sig) = Sig.runSignature (F.fresh (F.defaultAttribs "c" 0) { F.symIsCompound = True }) (Prob.signature prob)
          wdg   = estimatedDependencyGraph defaultApproximation prob
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
--- 'Knowledge propagation'

data SimpKP p = SimpKP
data SimpKPSelection = 
  SimpKPSelection { skpNode :: NodeId -- ^ Node of selected rule in the dependency graph
                  , skpRule :: Rule -- ^ Selected rule
                  , skpPredecessors :: [(NodeId,Rule)]-- ^ Predecessors of rules 
                  }
  
data SimpKPProof p = 
  SimpKPProof { skpDG            :: DG
              , skpSelections    :: [SimpKPSelection]
              , skpSig           :: F.Signature
              , skpVars          :: V.Variables}                                
  | SimpKPPProof { skpDG            :: DG
                 , skpSig           :: F.Signature
                 , skpPProof        :: P.PartialProof (P.ProofOf p)
                 , skpPProc         :: P.InstanceOf p                   
                 , skpSelections    :: [SimpKPSelection]
                 , skpVars          :: V.Variables}                                
                   
  | SimpKPErr DPError
                       
instance P.Processor p => T.TransformationProof (SimpKP p) where
  answer proof = 
    case T.transformationProof proof of
      SimpKPErr _ -> P.MaybeAnswer 
      SimpKPProof {} -> T.answerFromSubProof proof
      tproof@SimpKPPProof{} ->  
        case u1 `Cert.add` u2 of 
          Cert.Unknown -> P.MaybeAnswer
          u -> P.CertAnswer $ Cert.certified ( Cert.constant, u)
        where ub p = Cert.upperBound $ P.certificate p
              u1 = ub $ skpPProof tproof
              u2 = ub $ T.answerFromSubProof proof

  pprintTProof _ _ (SimpKPErr e) _ = pprint e
  pprintTProof _ _ p@(SimpKPProof {}) _ 
     | null sel = text "Knowledge propagation is not applicable on selected rules."
     | otherwise = 
      text "We consider the (estimated) dependency graph" 
      $+$ text ""
      $+$ indent (pprint (dg, sig, vars))
      $+$ paragraph "We estimate the application of rules based on the application of their predecessors as follows:"
      $+$ hcat [ let n = pprintNodeSet [skpNode s]
                 in text "- We remove" <+> n
                    <+> text "and add"
                    <+> text "Pre" <> parens n
                    <+> text "=" 
                    <+> pprintNodeSet [m | (m,_) <- skpPredecessors s]
                    <+> text "to the strict component."
                    $+$ text ""
                | s <- sel]
    where vars  = skpVars p                              
          sig   = skpSig p
          dg    = skpDG p
          sel   = skpSelections p
  pprintTProof _ _ p@(SimpKPPProof {}) _ = 
      ppSub 
      $+$ text ""
      $+$ if null sel
           then paragraph "The strictly oriented rules are moved into the corresponding weak component(s)."
           else paragraph (show $ text "Processor" 
                                   <+> text pName 
                                   <+> text "induces the complexity certificate "
                                   <+> pprint ans
                                   <+> text "on application of rules" 
                                   <+> pprintNodeSet (Set.toList orientedNodes) <> text "."
                                   <+> text "Here rules are labeled according to the (estimated) dependency graph")
                $+$ text ""
                $+$ indent (pprint (dg, sig, vars))
                $+$ text ""
                $+$ ppPropagates orientedNodes sel
                $+$ text ""
                $+$ paragraph (show $ text "Overall, we obtain that"
                                  <+> text "the number of applications of rules" 
                                  <+> pprintNodeSet (Set.toList knownNodes)
                                  <+> text "is given by"
                                  <+> pprint ans <> text "."
                                  <+> text "The rules are shifted into the corresponding weak component(s).")
    where vars  = skpVars p                              
          sig   = skpSig p
          dg    = skpDG p
          sel   = skpSelections p
          pproof = skpPProof p
          ans = P.answer pproof
          pName = "'" ++ P.instanceName (skpPProc p) ++ "'"
          dps = Trs.fromRules $ P.ppRemovableDPs pproof
          ldps = [(n,r) | (n, (_, r)) <- lnodes dg, Trs.member dps r]
          trs = Trs.fromRules $ P.ppRemovableTrs pproof
          orientedNodes = Set.fromList [ n | (n,_) <- ldps]
          knownNodes = orientedNodes `Set.union` Set.fromList [ skpNode s | s <- sel]
          ppSub | not $ P.progressed pproof = paragraph $ "Application of processor " ++ pName ++ " failed."
                | otherwise =                 
             paragraph ("We use the processor " 
                        ++ pName ++ " to orient following rules strictly. ")
             $+$ text ""
             $+$ pprintLabeledRules "DPs" sig vars ldps
             $+$ pprintNamedTrs sig vars "Trs" trs
             $+$ text ""
             $+$ block' "Sub-proof" [P.pprintProof pproof P.ProofOutput]

          ppPropagates _ [] = PP.empty
          ppPropagates sofar ss =
            text "-" <+> paragraph ("The rules " ++ (sns sofar) ++ " have known complexity. "
                                    ++ "These cover all predecessors of " ++ (sns newnodes) ++ ", their complexity is equally bounded.")
            $+$ ppPropagates (sofar `Set.union` newnodes) ss'
            where sns = show . pprintNodeSet . Set.toList
                  (new,ss') = partition predsCovered ss
                  predsCovered s = all (\ (n,_) -> n `Set.member` sofar) $ skpPredecessors s
                  newnodes = Set.fromList [skpNode s | s <- new]
            

instance (P.Processor p) => T.Transformer (SimpKP p) where 
  name _ = "simpKP"
  type ArgumentsOf (SimpKP p) = Arg (Assoc (RS.ExpressionSelector)) :+: Arg (Maybe (Proc p))
  type ProofOf (SimpKP p)     = SimpKPProof p
  arguments _ =       
    opt { A.name         = "select" 
        , A.defaultValue = RS.selAllOf RS.selDPs
        , A.description  = "Determines which rules to select. Per default all dependency pairs are selected for knowledge propagation."
        }
    :+: opt { A.name = "relative-processor"
            , A.defaultValue = Nothing
            , A.description = "If given, used to orient predecessors of selected rules."
            }

  description SimpKP = [unwords [ "Moves a strict dependency into the weak component"
                                , "if all predecessors in the dependency graph are strict" 
                                , "and there is no edge from the rule to itself."
                                , "Only applicable if the strict component is empty."]
                       ]
  transform inst prob 
     | not (Trs.isEmpty strs)      = return $ T.NoProgress $ SimpKPErr ContainsStrictRule
     | not $ Prob.isDPProblem prob = return $ T.NoProgress $ SimpKPErr $ NonDPProblemGiven
     | otherwise = transform' mpinst
    where wdg   = estimatedDependencyGraph defaultApproximation prob
          selector :+: mpinst = T.transformationArgs inst
          strs  = Prob.strictTrs prob
          sdps  = Prob.strictDPs prob
          wdps  = Prob.weakDPs prob

          mkSel n rl preds = SimpKPSelection { skpNode = n
                                             , skpRule = rl
                                             , skpPredecessors = [ (m,rlm) | (m, (_,rlm), _) <- preds] }

          transform' Nothing | null selected = return $ T.NoProgress proof
                             | otherwise     = return $ T.Progress proof (enumeration' [prob'])
               where selected = select (sort candidates) []
                     select []     sel = sel
                     select (c:cs) sel = select cs sel' 
                       where sel' | any (c `isPredecessorOf`) sel = sel
                                  | otherwise = c:sel
                             s1 `isPredecessorOf` s2 = skpNode s2 `elem` reachablesBfs wdg [skpNode s1]
                     sort cs = reverse $ catMaybes [ find (\ c -> skpNode c == n) cs | n <- topsort wdg]
                  
                     initialDPs = fst $ RS.rules $ RS.rsSelect (RS.selFirstAlternative selector) prob
                     candidates = [ mkSel n rl preds
                                  | (n,(StrictDP, rl)) <- lnodes wdg
                                  , Trs.member initialDPs rl 
                                  , let preds = lpredecessors wdg n
                                  , all (\ (m,(strictness,_),_) -> m /= n && strictness == StrictDP) preds ]
                     proof :: T.ProofOf (SimpKP p)
                     proof = SimpKPProof { skpDG   = wdg
                                         , skpSelections = selected
                                         , skpSig  = Prob.signature prob 
                                         , skpVars = Prob.variables prob}
                     shiftStrict = Trs.fromRules [r | s <- selected , (_,r) <- skpPredecessors s ]
                     shiftWeak   = Trs.fromRules [ skpRule s | s <- selected ]
                     prob' = prob { Prob.strictDPs = (sdps Trs.\\ shiftWeak) `Trs.union` shiftStrict
                                  , Prob.weakDPs   = (wdps `Trs.union` shiftWeak) Trs.\\ shiftStrict }
          transform' (Just pinst) = do
                pp <- P.solvePartial pinst (withPredecessors $ RS.rsSelect selector prob) prob
                return $ mkProof pinst pp
            where withPredecessors (P.SelectDP d) = P.BigOr [ P.SelectDP d, oneOfPreds]
                       where oneOfPreds = 
                               case lookupNode wdg (StrictDP, d) of 
                                  Just n -> P.BigOr [ P.SelectDP d, withPreds n (Set.singleton n)]
                                  Nothing -> P.BigAnd []
                  withPredecessors (P.SelectTrs _) = P.BigAnd []
                  withPredecessors (P.BigOr ss) = P.BigOr [withPredecessors s | s <- ss]
                  withPredecessors (P.BigAnd ss) = P.BigAnd [withPredecessors s | s <- ss]

                  withPreds n seen = bigAnd [ if n' `Set.member` seen 
                                               then P.SelectDP r'
                                               else P.BigOr [P.SelectDP r', withPreds n' (n' `Set.insert` seen) ] 
                                            | (n',r') <- preds ]
                    where preds = snub [ (n', r') | (n',(_,r'),_) <- lpredecessors wdg n]
                          bigAnd [a] = a
                          bigAnd as  = P.BigAnd as


                  mkProof :: P.Processor p => P.InstanceOf p -> P.PartialProof (P.ProofOf p) -> T.Result (SimpKP p)
                  mkProof proc p | progressed = T.Progress proof (enumeration' [prob'])
                                 | otherwise  = T.NoProgress proof 
                     where proof = SimpKPPProof { skpDG         = wdg
                                                , skpSelections = propagated
                                                , skpSig        = Prob.signature prob
                                                , skpPProof     = p
                                                , skpPProc      = proc
                                                , skpVars       = Prob.variables prob}

                           (known, propagated) = propagate (Trs.fromRules $ P.ppRemovableDPs p) []
                           propagate seen props
                                | null newp = (seen, props)
                                | otherwise = propagate (newr `Trs.union` seen) (newp ++ props)
                             where newr = Trs.fromRules [ skpRule s | s <- newp]
                                   newp = [ mkSel n rl preds
                                          | (n,(_, rl)) <- lnodes wdg
                                          , not (Trs.member seen rl)
                                          , let preds = lpredecessors wdg n
                                          , all (\ (_,(_,rl'),_) -> Trs.member seen rl') preds]

                           shiftWeak = sdps `Trs.intersect` known
                           progressed = not (Trs.isEmpty shiftWeak)
                           prob' = prob { Prob.strictDPs = (sdps Trs.\\ shiftWeak)
                                        , Prob.weakDPs   = (wdps `Trs.union` shiftWeak) }
         

simpKPProcessor :: T.Transformation (SimpKP P.AnyProcessor) P.AnyProcessor
simpKPProcessor = T.Transformation SimpKP

-- | Moves a strict dependency into the weak component
-- if all predecessors in the dependency graph are strict 
-- and there is no edge from the rule to itself.
-- Only applicable if the strict component is empty.
-- This processor is inspired by Knowledge Propagation used in AProVE, 
-- therefor its name.
simpKP :: T.TheTransformer (SimpKP P.AnyProcessor)
simpKP = T.Transformation SimpKP `T.withArgs` (RS.selAllOf RS.selDPs :+: Nothing)

simpKPOn :: RS.ExpressionSelector -> T.TheTransformer (SimpKP P.AnyProcessor)
simpKPOn rs = T.Transformation SimpKP `T.withArgs` (rs :+: Nothing)


withKPOn :: P.Processor p => P.InstanceOf p -> RS.ExpressionSelector -> T.TheTransformer (SimpKP p)
inst `withKPOn` rs = T.Transformation SimpKP `T.withArgs` (rs :+: Just inst)


----------------------------------------------------------------------
-- Trivial

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
     text "We consider the dependency graph"
     $+$ text ""
     $+$ indent (pprintCWDG cwdg sig vars ppLabel)
     $+$ text ""
     $+$ paragraph "All SCCs are trivial and dependency pairs can be removed."
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
  transform _ prob 
     | not $ Trs.isEmpty $ Prob.strictTrs prob = return $ T.NoProgress $ TrivialError $ ContainsStrictRule
     | not $ Prob.isDPProblem prob = return $ T.NoProgress $ TrivialError $ NonDPProblemGiven
     | cyclic    = return $ T.NoProgress proof
     | otherwise = return $ T.Progress proof (enumeration' [prob'])
        where cyclic = any (isCyclicNode cwdg) (nodes cwdg)
              wdg   = estimatedDependencyGraph defaultApproximation prob
              cwdg  = toCongruenceGraph wdg
              sig   = Prob.signature prob
              vars  = Prob.variables prob
              proof = TrivialProof { trivialCDG = cwdg
                                   , trivialSig = sig
                                   , trivialVars = vars }
              prob' = prob { Prob.strictDPs = Trs.empty
                           , Prob.weakDPs = Trs.empty }
                

trivialProcessor :: T.Transformation Trivial P.AnyProcessor
trivialProcessor = T.Transformation Trivial

-- | Checks whether the DP problem is trivial, i.e., does not contain any cycles.
--  
-- Only applicable on DP-problems as obtained by 'dependencyPairs' or 'dependencyTuples'. Also 
-- not applicable when @strictTrs prob \= Trs.empty@.
trivial :: T.TheTransformer Trivial
trivial = T.Transformation Trivial `T.withArgs` ()


----------------------------------------------------------------------
-- Inapplicable

data RemoveInapplicableReason = NonBasic

data RemoveInapplicable = RemoveInapplicable
data RemoveInapplicableProof = 
  RemoveInapplicableProof { riWDG   :: DG -- ^ Employed congruence graph.
                          , riRemoveds :: [(RemoveInapplicableReason,[(NodeId,Rule)])] -- ^ Rules that can be removed
                          , riSig   :: F.Signature
                          , riVars  :: V.Variables}
  | RemoveInapplicableError DPError
  | RemoveInapplicableFail
                       
instance T.TransformationProof RemoveInapplicable where
  answer = T.answerFromSubProof
  pprintTProof _ _ (RemoveInapplicableError e) _ = pprint e
  pprintTProof _ _ RemoveInapplicableFail _ = text "The DP problem could not be simplified."
  pprintTProof _ _ p _ = hcat [pp reason rs | (reason,rs) <- riRemoveds p]
     where pp NonBasic rs = 
             text "Consider the dependency graph:"
             $+$ text ""
             $+$ indent (pprint (wdg,sig,vars))
             $+$ text ""
             $+$ paragraph (show $ text "Left-hand sides of rules" 
                                   <+> pprintNodeSet [n | (n,_) <- rs] <+> text "are not (marked) basic terms."
                                   <+> text "Since for each rule there are no incoming edges from different nodes,"
                                   <+> text "these rules can be removed.")
           vars         = riVars p                              
           sig          = riSig p
           wdg          = riWDG p

instance T.Transformer RemoveInapplicable where
  name RemoveInapplicable        = "removeInapplicable"
  description RemoveInapplicable = [unwords [ "Removes rules that are not applicable in DP derivations."
                                 , "Only applicable if the strict component is empty."]
                        ]
  
  type ArgumentsOf RemoveInapplicable = Unit
  type ProofOf RemoveInapplicable = RemoveInapplicableProof
  arguments RemoveInapplicable = Unit
  transform _ prob 
     | not $ Trs.isEmpty $ Prob.strictTrs prob = return $ T.NoProgress $ RemoveInapplicableError $ ContainsStrictRule
     | not $ Prob.isDPProblem prob = return $ T.NoProgress $ RemoveInapplicableError $ NonDPProblemGiven
     | Trs.isEmpty removedRules = return $ T.NoProgress RemoveInapplicableFail
     | otherwise = return $ T.Progress proof (enumeration' [prob'])
        where wdg   = estimatedDependencyGraph defaultApproximation prob
              sig   = Prob.signature prob
              vars  = Prob.variables prob
              constrs = Prob.constrs $ Prob.startTerms prob
              removedRules = Trs.unions [Trs.fromRules [r | (_,rs) <- removeds
                                                          , (_,r) <- rs]]
              removeds = [( NonBasic
                          , [(n,r) | (n, (_,r)) <- lnodes wdg
                                   , all ((==) n) $ predecessors wdg n
                                   , any (\ a -> not $ functionSymbols a `Set.isSubsetOf` constrs) (properSubterms $ lhs r) 
                            ])
                         ]
              prob' = prob { Prob.strictDPs = Prob.strictDPs prob Trs.\\ removedRules
                           , Prob.weakDPs = Prob.weakDPs prob Trs.\\ removedRules }
              proof = RemoveInapplicableProof { riWDG = wdg
                                              , riSig = sig
                                              , riRemoveds = removeds
                                              , riVars = vars }
                

removeInapplicableProcessor :: T.Transformation RemoveInapplicable P.AnyProcessor
removeInapplicableProcessor = T.Transformation RemoveInapplicable

-- | Removes inapplicable rules in DP deriviations.
--  
-- Currently we check whether the left-hand side is non-basic, 
-- and there exists no incoming edge except from the same rule.
removeInapplicable :: T.TheTransformer RemoveInapplicable
removeInapplicable = T.Transformation RemoveInapplicable `T.withArgs` ()
