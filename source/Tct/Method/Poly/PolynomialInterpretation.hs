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

module Tct.Method.Poly.PolynomialInterpretation where

import Data.Typeable
import qualified Data.Map as Map

import Qlogic.PropositionalFormula
import Qlogic.Semiring

import qualified Termlib.FunctionSymbol as F
import qualified Termlib.Variable as V

import Tct.Encoding.Polynomial

data PolyInter a = PI { signature :: F.Signature
                      , interpretations :: Map.Map F.Symbol (VPolynomial a) }

data PIVar = PIVar { restrict :: Bool
                   , varfun :: F.Symbol
                   , argpos :: [Power V.Variable] }
                   deriving (Eq, Ord, Show, Typeable)

type VPolynomial a = Polynomial V.Variable a
type VMonomial a = Monomial V.Variable a

instance PropAtom PIVar

linearPolynomial :: RingConst a => F.Symbol -> F.Signature -> VPolynomial a
linearPolynomial f sig = Poly $ foldr (\i p -> ithmono i:p) [Mono (ringvar $ PIVar False f []) []] [1..a]
  where a = F.arity sig f
        ithmono i = Mono (ringvar $ PIVar False f [Pow (V.Canon i) 1]) [Pow (V.Canon i) 1]
