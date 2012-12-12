{- | 
Module      :  Tct.Encoding.UsableRules
Copyright   :  (c) Martin Avanzini <martin.avanzini@uibk.ac.at>, 
               Georg Moser <georg.moser@uibk.ac.at>, 
               Andreas Schnabl <andreas.schnabl@uibk.ac.at>
License     :  LGPL (see COPYING)

Maintainer  :  Martin Avanzini <martin.avanzini@uibk.ac.at>
Stability   :  unstable
Portability :  unportable      

This module implements a SAT encoding of usable rules
with respect to the argument filtering encoding, 
cf. module "Tct.Encoding.ArgumentFiltering".
-}

{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}

module Tct.Encoding.UsableRules 
       (
         validUsableRulesEncoding
         -- | Add this constraint for a valid SAT encoding.
       , usable 
         -- | Propositional formula that holds if the given rule is 
         -- usable.
       , initialUsables
         -- | Initial left-hand side roots symbols of usable rules.
       , usablef
         -- MS
       )
       where


import Prelude hiding ((||),(&&),not)
import Data.Typeable
import qualified Data.Set as Set

import Qlogic.SatSolver
import Qlogic.PropositionalFormula
import Qlogic.Boolean
import Qlogic.MemoizedFormula

import Termlib.Term (Term(..), root)
import qualified Termlib.Trs as Trs
import Termlib.Problem (Problem(..))
import qualified Termlib.Rule as Rule
import qualified Termlib.Problem as Prob
import Termlib.FunctionSymbol (Symbol)

data UsableAtom = UsableAtom Symbol
            deriving (Eq, Ord, Show, Typeable)
                     
instance PropAtom UsableAtom 

usablef :: Boolean b => (UsableAtom -> b) -> Problem -> Rule.Rule -> b
usablef atomf prob | not (Prob.isDPProblem prob) = const top                      
                   | otherwise                 = \ r -> usable' (root (Rule.lhs r))
  where usable' (Right f) | f `Set.member` ds = top
                          | otherwise         = atomf $ UsableAtom f
        usable' _         = top
        ds = case Prob.startTerms prob of 
               st@Prob.BasicTerms {} -> Prob.defineds st
               _                     -> error "UsableRules: Prob.defineds not defined on TermAlgebra"

usable :: (Eq l, Ord l) => Problem -> Rule.Rule -> PropFormula l
usable prob | not (Prob.isDPProblem prob) = const top                      
            | otherwise                 = \ r -> usable' (root (Rule.lhs r))
  where usable' (Right f) | f `Set.member` ds = top
                          | otherwise         = propAtom $ UsableAtom f
        usable' _         = top
        ds = case Prob.startTerms prob of 
               st@Prob.BasicTerms {} -> Prob.defineds st
               _                     -> error "UsableRules: Prob.defineds not defined on TermAlgebra"
                  
initialUsables :: [Symbol]
initialUsables = []

validUsableRulesEncoding :: (Eq l, Ord l, Monad s, Solver s l) => Problem -> (Symbol -> Int -> PropFormula l) -> Memo Term s l (PropFormula l)
validUsableRulesEncoding prob unfiltered 
  | Prob.isDPProblem prob = bigAnd [ usableM r --> omega (Rule.rhs r) | r <- Trs.rules allRules ]
  | otherwise             = top
     where omega = memoized $ \ t -> 
             case t of 
               Var _    -> top
               Fun f ts -> bigAnd [ usableM rl | rl <- Trs.rules $ Trs.definingSymbol allRules f]
                          && bigAnd [ unfilteredM f i --> omega ti | (i,ti) <- zip [1..] ts]
           
           usableM = return . usable prob
           unfilteredM f i = return $ unfiltered f i
           allRules = Prob.allComponents prob
           -- rhss trs = nubs $ [Rule.rhs r | r <- Trs.rules trs]
           --   where nubs = Set.toList . Set.fromList
                         

instance Decoder [Symbol] UsableAtom where 
  add (UsableAtom f) = (:) f
