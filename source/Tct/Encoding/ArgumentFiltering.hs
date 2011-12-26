{- | 
Module      :  Tct.Encoding.ArgumentFiltering
Copyright   :  (c) Martin Avanzini <martin.avanzini@uibk.ac.at>, 
               Georg Moser <georg.moser@uibk.ac.at>, 
               Andreas Schnabl <andreas.schnabl@uibk.ac.at>,
License     :  LGPL (see COPYING)

Maintainer  :  Martin Avanzini <martin.avanzini@uibk.ac.at>
Stability   :  unstable
Portability :  unportable      

This module provides a SAT encoding of argument filterings.
By convention, n-ary function symbols admit argument positions '[1..n]'.
-}

{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Tct.Encoding.ArgumentFiltering 
    ( validSafeArgumentFiltering
      -- | Add this constraint for a valid SAT encoding.      
    , isCollapsing
      -- | This formula holds if the argument filtering collapses 
      -- on the symbol.
    , isInFilter
      -- | The formula @isInFilter f i@ holds if the ith argument 
      -- filtering is in the filtering.
    , initial
    -- | Initial argument filtering.
    )
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
