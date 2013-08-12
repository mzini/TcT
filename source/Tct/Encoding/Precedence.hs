{- | 
Module      :  Tct.Encoding.Precedence
Copyright   :  (c) Martin Avanzini <martin.avanzini@uibk.ac.at>, 
               Georg Moser <georg.moser@uibk.ac.at>, 
               Andreas Schnabl <andreas.schnabl@uibk.ac.at>
License     :  LGPL (see COPYING)

Maintainer  :  Martin Avanzini <martin.avanzini@uibk.ac.at>
Stability   :  unstable
Portability :  unportable      

This module implements a SAT encoding of quasi precedences.
-}

{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}

module Tct.Encoding.Precedence 
    ( 
      validPrecedenceM
      -- | Add this constraint for a valid SAT encoding.      
    , encodeRecDepthM      
      -- | Initial constraints on recursion depth encoding
    , restrictRecDepthM      
      -- | Restrict the recursion depth to a given bound
    , precGt
      -- | 'f ``precGt`` g` asserts that 'f' is strictly 
      -- above 'g' in the precedence
    , precEq
      -- | Assert equivalence in the precedence.      
    , initial
      -- | The initial argument filtering.
      
      -- * Recursive Symbols
      -- |  This is used by "Tct.Method.PopStar" to 
      -- obtain a more precise complexity certificate
    , RecursiveSymbols (..)
    , initialRecursiveSymbols
    , isRecursive)
where
import Data.Typeable (Typeable)
import qualified Data.Set as Set

import qualified Termlib.Precedence as Prec
import Termlib.Precedence (Precedence, Order(..))
import Qlogic.Formula hiding (size)
import Qlogic.Boolean
import Prelude hiding ((&&),(||),not)
import Qlogic.PropositionalFormula
import Qlogic.NatSat (mGrt,mEqu,Size(..),natAtom, toFormula, natToFormula, NatFormula)
import Termlib.FunctionSymbol (Symbol, Signature)
import Qlogic.SatSolver

instance PropAtom (Order Symbol)

data Rank = Rank Symbol deriving (Typeable, Show, Eq, Ord)
instance PropAtom Rank

data RecDepth = RecDepth Symbol deriving (Typeable, Show, Eq, Ord)
instance PropAtom RecDepth

data IsRecursive = IsRecursive Symbol deriving (Typeable, Show, Eq, Ord)
instance PropAtom IsRecursive

newtype RecursiveSymbols = RS (Set.Set Symbol)

initial :: Signature -> Precedence
initial = Prec.empty

initialRecursiveSymbols :: RecursiveSymbols
initialRecursiveSymbols = RS Set.empty
  
gt :: Eq l => Symbol -> Symbol -> PropFormula l
f `gt` g = propAtom $ f :>: g

eq :: Eq l => Symbol -> Symbol -> PropFormula l
f `eq` g = propAtom $ f :~: g

precGt :: Eq l => Symbol -> Symbol -> PropFormula l
f `precGt` g | f == g          = Bot 
             | otherwise      = f `gt` g

precEq :: Eq l => Symbol -> Symbol -> PropFormula l
f `precEq` g | f == g     = Top
             | f < g     = f `eq` g
             | otherwise = g `eq` f

isRecursive :: Eq l => Symbol -> PropFormula l
isRecursive = propAtom . IsRecursive

validPrecedenceM :: (Eq l, Monad s, Solver s l) => [Symbol] -> SatSolver s l (PropFormula l)
validPrecedenceM []   = return $ Top
validPrecedenceM syms = toFormula constraint
    where rank sym     = natAtom size (Rank sym)
          size         = Bound $ length syms
          constraint   = bigAnd [ bigAnd [ f `mgt` g --> rank f `mGrt` rank g
                                         , g `mgt` f --> rank g `mGrt` rank f
                                         , f `meq` g --> rank f `mEqu` rank g]
                                | f <- syms, g <- syms,  f < g ]
          f `mgt` g = return $ f `gt` g
          f `meq` g = return $ f `eq` g
          
          
recDepth :: Eq l => Int -> Symbol -> NatFormula l
recDepth maxrd sym = natAtom (Bound $ max 1 maxrd) (RecDepth sym)

encodeRecDepthM :: (Eq l, Monad s, Solver s l) => [Symbol] -> Int -> SatSolver s l (PropFormula l)
encodeRecDepthM syms bound = toFormula $ 
  bigAnd [ isRecursiveM f --> recdepth f `mGrt` natToFormula 0 | f <- syms]
  && 
  bigAnd [ bigAnd [ f `mgt` g --> f `recGt` g
                  , g `mgt` f --> g `recGt` f
                  , f `meq` g --> (recdepth f `mEqu` recdepth g)]
         | f <- syms, g <- syms,  f < g ]
  where
    recdepth = recDepth bound
    isRecursiveM = return . isRecursive
    isNonRecursiveM = not . isRecursiveM 
    f `recGt` g = recdepth f `mGrt` recdepth g 
                  || (isNonRecursiveM f && recdepth f `mEqu` recdepth g)
    f `mgt` g = return $ f `gt` g
    f `meq` g = return $ f `eq` g  

restrictRecDepthM :: (Eq l, Monad s, Solver s l) => [Symbol] -> Int -> SatSolver s l (PropFormula l)
restrictRecDepthM syms bound = toFormula $ 
  bigAnd [ natToFormula (bound + 1) `mGrt` recdepth f | f <- syms]
  where
    recdepth = recDepth bound

          
instance Decoder Precedence (Order Symbol) where
  add = Prec.insert


instance Decoder RecursiveSymbols IsRecursive where
  add (IsRecursive f) (RS fs) = RS (f `Set.insert` fs)
