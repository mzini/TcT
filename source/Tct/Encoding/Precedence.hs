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
    , precEq)
where
import Termlib.Precedence
import Qlogic.Formula hiding (size)
import Qlogic.Boolean
import Prelude hiding ((&&),(||),not)
import Qlogic.PropositionalFormula
import Qlogic.NatSat (mGrt,mEqu,Size(..),natAtom, toFormula, natToFormula)
import Termlib.FunctionSymbol (Symbol)
import Qlogic.SatSolver

instance PropAtom (Order Symbol)
instance PropAtom Symbol

gt :: Eq l => Symbol -> Symbol -> PropFormula l
f `gt` g = propAtom $ f :>: g

eq :: Eq l => Symbol -> Symbol -> PropFormula l
f `eq` g = propAtom $ f :~: g

-- TODO: AS:AM: think about monadic code
validPrecedenceM :: (Eq l, Monad s, Solver s l) => [Symbol] -> Maybe Int -> SatSolver s l (PropFormula l)
validPrecedenceM []   _      = return $ Top
validPrecedenceM syms mbound = toFormula constraint
    where rank sym   = natAtom size sym
          size       = Bound $ length syms
          constraint = bigAnd [ bigAnd [ f `mgt` g --> rank f `mGrt` rank g
                                       , g `mgt` f --> rank g `mGrt` rank f
                                       , f `meq` g <-> rank f `mEqu` rank g]
                              | f <- syms, g <- syms,  f < g ]
                       && maybe top restrictRanks mbound
          restrictRanks bound = bigAnd [ natToFormula (bound + 1) `mGrt` rank f | f <- syms]
          f `mgt` g = return $ f `gt` g
          f `meq` g = return $ f `eq` g
          

precGt :: Eq l => Symbol -> Symbol -> PropFormula l
f `precGt` g | f == g          = Bot 
             | otherwise      = f `gt` g

precEq :: Eq l => Symbol -> Symbol -> PropFormula l
f `precEq` g | f == g     = Top
             | f < g     = f `eq` g
             | otherwise = g `eq` f

instance Decoder Precedence (Order Symbol) where
  add = insert
