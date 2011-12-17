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
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Tct.Encoding.UsableRules 
       (
         validUsableRulesEncoding
       , usable 
       , initialUsables
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