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
{-# LANGUAGE FlexibleInstances #-}

module Tct.Encoding.Precedence 
    ( validPrecedenceM
    , precGt
    , precEq
    , isRecursive
--    , isRecursive
    , RecursiveSymbols (..)
    , initial
    , initialRecursiveSymbols)
where
import Data.Typeable (Typeable)
import qualified Data.Set as Set

import qualified Termlib.Precedence as Prec
import Termlib.Precedence (Precedence, Order(..))
import Qlogic.Formula hiding (size)
import Qlogic.Boolean
import Prelude hiding ((&&),(||),not)
import Qlogic.PropositionalFormula
import Qlogic.NatSat (mGrt,mEqu,Size(..),natAtom, toFormula, natToFormula)
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

validPrecedenceM :: (Eq l, Monad s, Solver s l) => [Symbol] -> Maybe Int -> SatSolver s l (PropFormula l)
validPrecedenceM []   _      = return $ Top
validPrecedenceM syms mbound = toFormula constraint
    where rank sym     = natAtom size (Rank sym)
          recdepth sym = natAtom size (RecDepth sym)
          size         = Bound $ length syms
          constraint   = bigAnd [ bigAnd [ f `mgt` g --> rank f `mGrt` rank g
                                         , g `mgt` f --> rank g `mGrt` rank f
                                         , f `meq` g --> rank f `mEqu` rank g]
                                | f <- syms, g <- syms,  f < g ]
                         && maybe top restrictDepths mbound
          restrictDepths bound = bigAnd [ natToFormula (bound + 1) `mGrt` recdepth f 
                                          && (isRecursiveM f --> recdepth f `mGrt` natToFormula 0)
                                        | f <- syms]
                                 && bigAnd [ bigAnd [ f `mgt` g --> f `recGt` g
                                                   , g `mgt` f --> g `recGt` f
                                                   , f `meq` g --> (recdepth f `mEqu` recdepth g)]
                                          | f <- syms, g <- syms,  f < g ]
          f `mgt` g = return $ f `gt` g
          f `meq` g = return $ f `eq` g
          isRecursiveM = return . isRecursive
          isNonRecursiveM = not . isRecursiveM 
          f `recGt` g = recdepth f `mGrt` recdepth g 
                        || (isNonRecursiveM f && recdepth f `mEqu` recdepth g)
          
instance Decoder Precedence (Order Symbol) where
  add = Prec.insert


instance Decoder RecursiveSymbols IsRecursive where
  add (IsRecursive f) (RS fs) = RS (f `Set.insert` fs)
