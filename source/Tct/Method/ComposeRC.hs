{-# LANGUAGE FlexibleInstances #-}
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

{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DeriveDataTypeable #-}

module Tct.Method.ComposeRC where

import Control.Monad (liftM, mplus)
import Text.PrettyPrint.HughesPJ
import qualified Data.Set as Set
import qualified Data.Map as Map
import qualified Data.List as List
import Data.Maybe (catMaybes)

import qualified Tct.Processor as P
import qualified Tct.Processor.Transformations as T
import qualified Tct.Processor.Args as A
import Tct.Processor.PPrint
import Tct.Processor.Args
import Tct.Processor.Args.Instances
import qualified Tct.Certificate as Cert

import Termlib.Trs.PrettyPrint (pprintNamedTrs)
import Termlib.Utils (PrettyPrintable (..))
import qualified Termlib.Term as Term
import qualified Termlib.Trs as Trs
import qualified Termlib.Signature as Sig
import qualified Termlib.Variable as V
import Termlib.Rule (Rule(..))
import qualified Termlib.FunctionSymbol as F
import qualified Termlib.Problem as Prob
import Tct.Method.DP.DependencyGraph
import qualified Tct.Method.DP.DependencyGraph as DG
import Tct.Method.Compose hiding (progress)
import Data.Graph.Inductive.Query.DFS (dfs)
import Data.Typeable ()

data ComposeRCProc p1 p2 = ComposeRCProc

data ComposeRCProof p1 p2 = ComposeRCProof { cpRuleSelector :: RuleSelector ()
                                           , cpUnselected   :: Trs.Trs
                                           , cpSelected     :: Trs.Trs 
                                           , cpCut          :: Trs.Trs 
                                           , cpUncut        :: Trs.Trs 
                                           , cpProof1       :: Maybe (P.Proof p1) 
                                           , cpProof2       :: Maybe (P.Proof p2)
                                           , cpProb1        :: Prob.Problem
                                           , cpProb2        :: Prob.Problem
                                           , cpWdg          :: DG.DG
                                           , cpSig          :: F.Signature
                                           , cpVars         :: V.Variables }
                          | ComposeRCInapplicable String

progress :: (P.Processor p1, P.Processor p2) => ComposeRCProof p1 p2 -> Bool
progress ComposeRCInapplicable {} = False
progress proof = maybe True P.succeeded (cpProof1 proof) 
                 && maybe True P.succeeded (cpProof2 proof)
                 && not (Trs.isEmpty (cpCut proof)) 
                 && not (Trs.isEmpty (cpUncut proof))

instance AssocArgument (RuleSelector ()) where 
    assoc _ = [] -- TODO extend


instance (P.Processor p1, P.Processor p2) => T.Transformer (ComposeRCProc p1 p2) where
    type T.ArgumentsOf (ComposeRCProc p1 p2) = Arg (Assoc (RuleSelector ())) :+: Arg (Maybe (Proc p1)) :+: Arg (Maybe (Proc p2))
    type T.ProofOf (ComposeRCProc p1 p2)     = ComposeRCProof p1 p2

    name ComposeRCProc        = "compose-rc"
    instanceName inst   = show $ text "compose-rc" <+> parens (ppsplit)
        where split :+: _ = T.transformationArgs inst
              ppsplit = text $ show split 

    description ComposeRCProc = [ unwords [ ] ]
    arguments ComposeRCProc   = opt { A.name         = "split" 
                                    , A.defaultValue = selFirstStrictCongruence
                                    , A.description  = ""}
                                :+: opt { A.name = "subprocessor 1"
                                        , A.defaultValue = Nothing
                                        , A.description = ""}
                                :+: opt { A.name = "subprocessor 2"
                                        , A.defaultValue = Nothing
                                        , A.description = ""}

    transform inst prob | not (Prob.isDPProblem prob) = return $ T.NoProgress $ ComposeRCInapplicable "given problem is not a DP problem" 
                        | otherwise                 = do mproof1 <- mapply mproc1 prob1
                                                         mproof2 <- case maybe True P.succeeded mproof1 of 
                                                                     True  -> mapply mproc2 prob2
                                                                     False -> return Nothing
                                                         return $ mkProof mproof1 mproof2

        where s :+: mproc1 :+: mproc2 = T.transformationArgs inst 
              wdg = estimatedDependencyGraph Edg prob
              allLabeledNodes = lnodes wdg
              sig = Prob.signature prob

              mkProof mproof1 mproof2 | progress tproof = T.Progress tproof subprobs
                                      | otherwise       = T.NoProgress tproof
                  where tproof = ComposeRCProof { cpRuleSelector = s
                                                , cpUnselected   = unselectedDPs
                                                , cpSelected     = selectedStrictDPs `Trs.union` selectedWeakDPs
                                                , cpCut          = cutTrs
                                                , cpUncut        = uncutTrs
                                                , cpProof1       = mproof1
                                                , cpProof2       = mproof2
                                                , cpProb1        = prob1
                                                , cpProb2        = prob2
                                                , cpWdg          = wdg
                                                , cpSig          = sig'
                                                , cpVars         = Prob.variables prob }
                        subprobs = catMaybes [ maybe (Just (SN (1 :: Int), prob1)) (const Nothing) mproof1
                                             , maybe (Just (SN (2 :: Int), prob2)) (const Nothing) mproof2 ]

              prob1 = prob { Prob.signature = sig'
                           , Prob.strictDPs = uncutTrs
                           , Prob.weakDPs   = Trs.empty }

              prob2 = prob { Prob.signature = sig'
                           , Prob.strictDPs = selectedStrictDPs
                           , Prob.weakDPs   = Trs.unions [ cutTrs, uncutTrs, selectedWeakDPs ] }
              
              (selectedNodes, selectedStrictDPs, selectedWeakDPs) = 
                  (Set.fromList ns, Trs.fromRules rss, Trs.fromRules rsw)
                  where (ns,rsel) = unzip selected 
                        (rss,rsw) = foldl (\ (rss',rsw') (a,r) -> 
                                           case a of 
                                             DG.StrictDP -> (r : rss',rsw')
                                             DG.WeakDP   -> (rss', r : rsw')) ([],[]) rsel
                        selected = closeBySuccessor $ rsSelect s () prob
                        closeBySuccessor rs = [(n,dpnode) | (n, dpnode) <- withNodeLabels' wdg (dfs initials wdg) ]
                            where initials = [ n | (n, (_, r)) <- allLabeledNodes, Trs.member dps r ]
                                  dps = Prob.sdp rs `Trs.union` Prob.wdp rs

              unselectedDPs = (Prob.strictDPs prob Trs.\\ selectedStrictDPs)
                              `Trs.union` (Prob.weakDPs prob Trs.\\ selectedWeakDPs)
                              
              ((uncutTrs, cutTrs), sig') = 
                  flip Sig.runSignature sig $ 
                       do (uncuts,cuts) <- unzip `liftM` splitRulesM unselectedDPs
                          let toTrs = Trs.fromRules . catMaybes
                          return (toTrs uncuts, toTrs cuts)

              splitRulesM trs = mapM splitRuleM (Trs.toRules trs)
              splitRuleM  rl@(Rule l r@(Term.Fun f ts)) | F.isCompound sig f = mk (zip [1..] ts)
                                                        | otherwise          = mk (zip [1] [r])
                  where mk its = do rUncut <- mkrl "" uncut 
                                    rCut   <- mkrl "'" cut
                                    return (rUncut, rCut)
                            where (uncut,cut) = List.partition (\ (n,_) -> n `Set.member` uncutPositions) its
                        ruleToNode = Map.fromList [(rn,n) | (n, (_,rn)) <- allLabeledNodes]
                        uncutPositions = case Map.lookup rl ruleToNode of 
                                           Just n -> Set.fromList [ p | (m, _, p) <- lsuccessors wdg n, not $ m `Set.member` selectedNodes ]
                                           Nothing -> Set.empty

                        mkrl _ []  = return Nothing
                        mkrl _ [(_,t)] = return $ Just $ Rule l t
                        mkrl sn tis    = do attribs <- F.getAttributes f 
                                            c <- F.fresh attribs { F.symArity    = length ts
                                                                , F.symIsCompound = True 
                                                                , F.symIdent = F.symIdent attribs ++ sn}
                                            return $ Just $ Rule l (Term.Fun c [ti | (_, ti) <- tis])
              splitRuleM  rl  = return (Just rl, Nothing)

              mapply :: (P.Processor p, P.SolverM m) => Maybe (P.InstanceOf p) -> Prob.Problem -> m (Maybe (P.Proof p))
              mapply Nothing      _     = return Nothing
              mapply (Just proci) probi = Just `liftM` P.apply proci probi

instance (P.Processor p1, P.Processor p2) => T.TransformationProof (ComposeRCProc p1 p2) where
    pprintProof _ _ (ComposeRCInapplicable reason) = text "Compose RC is inapplicable since" <+> text reason
    pprintProof _ prob tproof = text "We measure the number of applications of following selected rules relative to the remaining rules"
                                $+$ text ""
                                $+$ indent (pptrs "Selected Rules (A)" (cpSelected tproof))
                                $+$ text ""
                                $+$ indent (pptrs "Remaining Rules (B)" (cpUnselected tproof))
                                $+$ text ""
                                $+$ text "These ruleset (A) was choosen by selecting function" 
                                $+$ indent (text (show (cpRuleSelector tproof)) <> text ",")
                                $+$ text "and closed under successors using the following dependency graph."
                                $+$ indent (pprint (cpWdg tproof, sig, vars))
                                $+$ text ""
                                $+$ text "The length of a single A-subderivation is expressed by the following problem."
                                $+$ text ""
                                $+$ block' "Problem A" [pprint (cpProb2 tproof)]
                                $+$ text ""
                                $+$ text "The number of B-applications is expressed by the following problem"
                                $+$ text ""
                                $+$ block' "Problem B" [pprint (cpProb1 tproof)]
                                $+$ maybePrintSub (cpProof1 tproof) "A"
                                $+$ maybePrintSub (cpProof2 tproof) "B"
       where sig = cpSig tproof
             vars = Prob.variables prob
             pptrs = pprintNamedTrs sig vars
             maybePrintSub :: P.Processor p => Maybe (P.Proof p) -> String -> Doc
             maybePrintSub Nothing  _ = empty
             maybePrintSub (Just p) n | P.succeeded p = text "We orient Problem" <+> text n 
                                                        $+$ indent (pprint p)
                                      | otherwise     = text "We did not obtain a certificate for Problem" <+> text n
                                                        $+$ text "We abort."

    answer proof = case (lb,ub) of 
                     (Cert.Unknown, Cert.Unknown) -> P.MaybeAnswer
                     _                            -> P.answerFromCertificate $ Cert.certified (Cert.Unknown, ub)
        where tproof = T.transformationProof proof
              subproofs = T.subProofs proof
              ub = Cert.upperBound cert1 `Cert.mult` Cert.upperBound cert2
              lb = Cert.lowerBound cert1 `Cert.add` Cert.lowerBound cert2
              cert1 = certFrom (cpProof1 tproof) (find (1 :: Int) subproofs)
              cert2 = certFrom (cpProof2 tproof) (find (2 :: Int) subproofs)
              certFrom :: (P.Answerable a1, P.Answerable a2) => Maybe a1 -> Maybe a2 -> Cert.Certificate
              certFrom mp1 mp2 = maybe Cert.uncertified id mcert 
                  where mcert = (P.certificate `liftM` mp1) `mplus` (P.certificate `liftM` mp2)

defaultSelect :: RuleSelector a
defaultSelect = s1
    where s1 = selBfs "admits strict predecessor in CDG" fn
              where fn cdg n = if any ((==) DG.StrictDP . fst) rs then [n] else []
                        where rs = DG.allRulesFromNodes cdg (DG.predecessors cdg n)

composeRCProcessor :: T.TransformationProcessor (ComposeRCProc P.AnyProcessor P.AnyProcessor) P.AnyProcessor
composeRCProcessor = T.transformationProcessor ComposeRCProc


composeRC :: RuleSelector () -> T.TheTransformer (ComposeRCProc P.SomeProcessor P.SomeProcessor)
composeRC s = ComposeRCProc `T.calledWith` (s :+: Nothing :+: Nothing)

solveAWith :: (P.Processor p1, P.Processor p2, P.Processor p3) => (T.TheTransformer (ComposeRCProc p1 p2)) -> P.InstanceOf p3 -> (T.TheTransformer (ComposeRCProc p1 p3))
solveAWith (T.TheTransformer _ (s :+: p1 :+: _)) p = T.TheTransformer ComposeRCProc (s :+: p1 :+: Just p)

solveBWith :: (P.Processor p1, P.Processor p2, P.Processor p3) => (T.TheTransformer (ComposeRCProc p1 p2)) -> P.InstanceOf p3 -> (T.TheTransformer (ComposeRCProc p3 p2))
solveBWith (T.TheTransformer _ (s :+: _ :+: p2)) p = T.TheTransformer ComposeRCProc (s :+: Just p :+: p2)