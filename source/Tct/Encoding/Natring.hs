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

{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeSynonymInstances #-}

module Encoding.Natring where

import qualified Qlogic.Arctic as Arc
import qualified Qlogic.ArcSat as AS
import qualified Qlogic.Diophantine as D
import Qlogic.Formula
import qualified Qlogic.NatSat as N
import Qlogic.Semiring

type GenSizeNatFormula l = N.Size -> N.NatFormula l
type GenSizeArcFormula l = AS.Size -> AS.ArcFormula l

instance Eq l => RingConst (GenSizeNatFormula l) where
  czero _ = N.natToFormula 0
  cone _ = N.natToFormula 1
  ringvar = flip N.natAtom . D.toDioVar
  restrictvar v _ = N.natAtom (N.Bound 1) $ D.toDioVar v

instance Eq l => RingConst (GenSizeArcFormula l) where
  czero _ = AS.arcToFormula zero
  cone _ = AS.arcToFormula one
  ringvar = flip AS.arcAtom . D.toDioVar
  restrictvar v _ = AS.arcAtom (AS.Bits 1) $ D.toDioVar v

instance Semiring b => RingConst (D.DioPoly D.DioVar b) where
  czero = D.constToPoly zero
  cone = D.constToPoly one
  ringvar = D.varToPoly . D.toDioVar
  restrictvar = D.restrictVarToPoly . D.toDioVar

instance RingConst (N.Size -> Int) where
  czero   = const 0
  cone    = const 1
  ringvar = const $ const 0
  restrictvar = const $ const 0

instance RingConst (AS.Size -> Arc.ArcInt) where
  czero   = const Arc.MinusInf
  cone    = const $ Arc.Fin 0
  ringvar = const $ const $ Arc.Fin 0
  restrictvar = const $ const $ Arc.Fin 0

-- instance Eq l => Semiring (N.NatFormula l) where
--   plus = (N..+.)
--   prod = (N..*.)
--   zero = N.natToFormula 0
--   one = N.natToFormula 1

instance (Eq a, Eq b, Semiring b) => Semiring (D.DioPoly a b) where
  plus = D.add
  prod = D.mult
  zero = D.constToPoly zero
  one = D.constToPoly one

-- instance Eq l => AbstrEq (N.NatFormula l) (PropFormula l) where
--   (.==.) = (N..=.)
-- 
-- instance Eq l => AbstrOrd (N.NatFormula l) (PropFormula l) where
--   (.<.)  = flip (N..>.)
--   (.<=.) = flip (N..>=.)
-- 
-- instance Eq l => AbstrOrdSemiring (N.NatFormula l) (PropFormula l)

instance (Eq l, Eq a, Eq b) => AbstrEq (D.DioPoly a b) (D.DioFormula l a b) where
  x .==. y = A (x `D.Equ` y)

instance (Eq l, Eq a, Eq b) => AbstrOrd (D.DioPoly a b) (D.DioFormula l a b) where
   x .<. y  = A (y `D.Grt` x)
   x .<=. y = A (y `D.Geq` x)

instance (Eq l, Eq b, Semiring b) => AbstrOrdSemiring (D.DioPoly D.DioVar b) (D.DioFormula l D.DioVar b)

instance AbstrEq Int Bool where
  (.==.) = (==)

instance AbstrOrd Int Bool where
  (.<.)  = (<)
  (.<=.) = (<=)

instance AbstrEq Arc.ArcInt Bool where
  (.==.) = (==)

instance AbstrOrd Arc.ArcInt Bool where
  (.<.)  = (Arc.<)
  (.<=.) = (Arc.<=)

instance AbstrOrdSemiring Int Bool

instance AbstrOrdSemiring Arc.ArcInt Bool
