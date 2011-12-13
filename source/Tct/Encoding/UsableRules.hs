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
       )
       where


import Prelude hiding ((||),(&&),not)
import Data.Typeable

import Qlogic.SatSolver
import Qlogic.PropositionalFormula
import Qlogic.Boolean
import Qlogic.MemoizedFormula

import Termlib.ArgumentFiltering
import Termlib.Term (Term(..), root)
import qualified Termlib.Trs as Trs
import Termlib.Problem (Problem(..))
import qualified Termlib.Rule as Rule
import qualified Termlib.Problem as Prob
import Termlib.FunctionSymbol (Symbol, Signature, argumentPositions, arity, isCompound, symbols)

import Tct.Encoding.ArgumentFiltering

data UsableAtom = UsableAtom Symbol
            deriving (Eq, Ord, Show, Typeable)
                     
instance PropAtom UsableAtom 

usable :: (Eq l, Ord l) => Rule.Rule -> PropFormula l
usable r = case root (Rule.lhs r) of 
             Right f -> propAtom $ UsableAtom f
             Left _  -> top

validUsableRulesEncoding :: (Eq l, Ord l, Monad s, Solver s l) => Problem -> (Symbol -> Int -> PropFormula l) -> Memo Term s l (PropFormula l)
validUsableRulesEncoding prob unfiltered = bigAnd [ omega (Rule.rhs r) | r <- stricts ]
                                           && bigAnd [ usableM r --> omega (Rule.rhs r) | r <- weaks ]
     where omega = memoized $ \ t -> 
             case t of 
               Var x    -> top
               Fun f ts -> bigAnd [ usableM rl | rl <- rulesDefining f]
                          && bigAnd [ return (unfiltered f i) --> omega ti | (i,ti) <- zip [1..] ts]
           rulesDefining f = [ r | r <- weaks, root (Rule.lhs r) == Right f ]
           weaks = Trs.rules $ Prob.weakTrs prob
           stricts = Trs.rules $ Prob.strictComponents prob           
           usableM = return . usable

-- instance Decoder [Symbol]  where 
--   add = insert