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

module Tct.Encoding.ArgumentFiltering 
    ( isCollapsing
    , isInFilter
    , initial
    , insert
    , validSafeArgumentFiltering)
where

import qualified Data.IntSet as IntSet
import qualified Data.Set as Set
import Prelude hiding ((||),(&&),not)
import Data.Typeable
import Qlogic.SatSolver
import Qlogic.PropositionalFormula
import Qlogic.Boolean
import Termlib.ArgumentFiltering
import Termlib.FunctionSymbol (Symbol, Signature, argumentPositions, arity, isCompound, symbols)

data AFAtom = Collapsing Symbol
            | InFilter Symbol Int deriving (Eq, Ord, Show, Typeable)

instance PropAtom AFAtom

isCollapsing :: (Eq l, Ord l) => Symbol -> PropFormula l
isCollapsing = propAtom . Collapsing 

isInFilter :: (Eq l, Ord l) => Symbol -> Int -> PropFormula l
isInFilter sym pos = propAtom $ InFilter sym pos


initial :: Signature -> ArgumentFiltering
initial sig = Set.fold (alter mk) (empty sig) $ symbols sig
  where mk _ = Just $ Filtering $ IntSet.empty

insert :: AFAtom -> ArgumentFiltering -> ArgumentFiltering
insert (Collapsing sym) af = alter f sym af
  where f Nothing              = Just $ Projection 0
        f (Just (Filtering s)) = case IntSet.elems s of
                                   [p] -> Just $ Projection p
                                   _   -> error "ArgumentFiltering.insert: collapsing on multiple positions"
        f _                    =  error "ArgumentFiltering.insert: The impossible Happened"
insert (InFilter sym pos) af = alter f sym af
  where f Nothing               = Just $ Filtering $ IntSet.singleton pos
        f (Just (Projection 0)) = Just $ Projection pos
        f (Just (Filtering s))  = Just $ Filtering $ IntSet.insert pos s
        f _                    =  error "ArgumentFiltering.insert: reassining collapsing position"

instance Decoder ArgumentFiltering AFAtom where add = insert

validSafeArgumentFiltering :: (Eq l, Ord l) => [Symbol] -> Signature -> PropFormula l
validSafeArgumentFiltering syms sig = forall syms assertValid
  where assertValid sym | arity sig sym == 0 = not $ isCollapsing sym
                        | isCompound sig sym = not (isCollapsing sym) && (forall (argumentPositions sig sym) $ \ pos -> isInFilter sym pos)
                        | otherwise          = isCollapsing sym --> exactlyOne [isInFilter sym pos | pos <- argumentPositions sig sym]
