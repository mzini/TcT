----------------------------------------------------------------------------------
-- |
-- Module      :  Tct.Method.Bounds.Violations.Find
-- Copyright   :  (c) Martin Avanzini <martin.avanzini@uibk.ac.at>, 
--                Georg Moser <georg.moser@uibk.ac.at>, 
--                Andreas Schnabl <andreas.schnabl@uibk.ac.at>
-- License     :  LGPL (see COPYING)
-- Maintainer  :  Martin Avanzini <martin.avanzini@uibk.ac.at>, 
--                Andreas Schnabl <andreas.schnabl@uibk.ac.at>
-- Stability   :  unstable
-- Portability :  unportable      
--
-- This module implements search for compatibility violations, as employed in
-- the bound processor.
----------------------------------------------------------------------------------

module Tct.Method.Bounds.Violations.Find where

import qualified Data.Set as Set
import qualified Data.Map as Map
import Data.Maybe (fromMaybe)
import Control.Monad (foldM, liftM, filterM)

import Termlib.Utils
import qualified Termlib.Rule as R
import Termlib.Term (Term(..), root, variables)
import qualified Termlib.Term as T
import Termlib.Rule (Strictness(..))
import qualified Termlib.Variable as Var

import Tct.Method.Bounds.Automata

decidingLabel :: Enrichment -> Strictness -> WeakBoundedness -> Label -> R.Rule -> LTerm -> Label
decidingLabel e str wb ml (R.Rule lhs rhs) = case e of {Top -> mtop; Match -> case str of {StrictRule -> mmatch; WeakRule -> mmatchrt}; Roof  -> mroof}
    where mtop   (F (_,l) _)    = l
          mtop   (S _)          = error "Bounds.decidingLabel.mtop: cannot determine label from state"
          mmatch (F (_,l) ts)   = foldl min l [ mmatch ti | ti <- ts, isFun ti]
              where isFun (F _ _) = True
                    isFun _       = False
          mmatch (S _)          = error "Bounds.decidingLabel.mmatch: cannot determine label from state"
          mmatchrt t@(F (_,l) _) = if rtApplicable then applyMaxLabel (l - 1) else applyMaxLabel (mmatch t)
                                      where rtApplicable = (T.size lhs >= T.size rhs) && equalLabels t
                                            equalLabels (F (_,l') ts) = l == l' && all equalLabels ts
                                            equalLabels (S _) = True
                                            applyMaxLabel lab = case wb of
                                                                  WeakMayExceedBound -> lab
                                                                  WeakMayNotExceedBound -> min (ml - 1) lab
          mmatchrt (S _)         = error "Bounds.decidingLabel.mmatchrt: cannot determine label from state"
          mroof  llhs              = mroof' lhs llhs
              where mroof' (Fun _ ts) (F (_,l) lts) = foldl min l [ mroof' ti lti | (ti,lti) <- zip ts lts, isRoof ti]
                    mroof'  s          t            = error $ "Bounds.decidingLabel.mroof': called with strange arguments " ++ show (pprint s) ++ " and " ++ show (pprint t)
                    isRoof (Var _) = False
                    isRoof u       = rvars `Set.isSubsetOf` variables u
                    rvars = variables rhs

reachableFromLifted :: Automaton -> Term -> Set.Set State -> Set.Set (LTerm, State)
reachableFromLifted a t qs = runMemoAction reachableFromLiftedM
    where t' = identifyVars t
          reachableFromLiftedM = foldM (\ r q ->
                                            do lterms <- reachLiftS (t',q)
                                               return $ r `Set.union` Set.map (\ lt -> (lt,q)) lterms)
                                 Set.empty $ Set.toList qs
          reachLiftS (Var _,      q)   = return $ Set.singleton $ S q
          reachLiftS s@(Fun f ts, q)   = memo (s,q) $
                                         (foldM (\ lterms (l,args) ->
                                                     Set.union lterms `liftM` labeledSubterms (f,l) (zip ts args)) 
                                          Set.empty  [(l, args) | (l,argss) <- bstepUL a f q , args <- Set.toList argss])
          labeledSubterms fl subproblems = do ltis <- mapM reachLiftS subproblems
                                              return $ Set.fromList $ [F fl lts | lts <- listProduct $ map Set.toList ltis]
          identifyVars (Var _) = Var (Var.canonical 0)
          identifyVars (Fun f ts) = Fun f $ map identifyVars ts

reaches :: Automaton -> LTerm -> State -> MemoAction (LTerm,State) Bool Bool
reaches _ (S p) q | p == q  = return $ True
                  | otherwise = return $ False
reaches a (F fl lts) q2 = foldM f False (Set.toList $ bstep a fl q2)
    where f True  _ = return True
          f False arg = foldM g True (zip lts arg)
          g False _ = return False
          g True (lti,qi) = memo (lti,qi) $ reaches a lti qi

findViolations :: Automaton -> Enrichment -> Strictness -> WeakBoundedness -> Label -> R.Rule -> Set.Set (LTerm, State)
findViolations a e str wb ml rule = Set.fromList $ runMemoAction $ filterM (\ (lt, q) -> not `liftM` candidateRejected lt q) candidates
    where candidates = snub [ (labeledRhs labeledLhs, q) | (labeledLhs, q) <- Set.toList $ reachableFromLifted a l qs]
          candidateRejected lt q = ifM (reaches a lt q) (return True) (isTrivialEpsilon lt q)
          isTrivialEpsilon (F _ _) _ = return False
          isTrivialEpsilon (S p) q = return (a == insert (Epsilon p q) a)
          rt = case root l of Right f' -> f'; Left  _ -> error "Bounds.violations: Encountered variable on left-hand side"
          qs = Set.unions [qs' | (_,_,qs') <- rulesDefiningUL a rt]
          l = R.lhs rule
          r = R.rhs rule
          labeledRhs labeledLhs = computeRhs (subst l labeledLhs) r
              where newLabel = (decidingLabel e str wb ml rule labeledLhs + 1)
                    subst (Var v)    (S s)     = Map.singleton v s
                    subst (Fun _ ts) (F _ lts) = Map.unions [subst ti lti | (ti,lti) <- zip ts lts]
                    subst _          _         = error "Bounds.violations: labeled term does not match left-hand side"
                    computeRhs s (Var v)       = S $ fromMaybe (error "Variables of right-hand side not included in variables of left-hand side") (Map.lookup v s)
                    computeRhs s (Fun f ts)    = F (f,newLabel) [computeRhs s ti | ti <- ts]
