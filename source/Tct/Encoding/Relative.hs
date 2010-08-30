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
{-# LANGUAGE MultiParamTypeClasses #-}

module Tct.Encoding.Relative 
    ( strictlyOriented
    , weaklyOriented
    , initialStrictRules
    , Orientation
    , StrictRules
    , trs)
where

import Data.Typeable
import Termlib.Term
import Termlib.Rule
import qualified Termlib.Trs as Trs
import Qlogic.SatSolver

import Qlogic.PropositionalFormula
import Termlib.Trs (Trs, union, singleton)

data Orientation = Strict (Term,Term)
                 | Weak (Term,Term) deriving (Eq, Ord, Typeable, Show)

newtype StrictRules = Sr {trs :: Trs}

strictlyOriented :: Rule -> Orientation
strictlyOriented = Strict . toPair

weaklyOriented :: Rule -> Orientation
weaklyOriented = Weak . toPair

initialStrictRules :: StrictRules 
initialStrictRules = Sr Trs.empty

instance PropAtom Orientation

instance Decoder StrictRules Orientation where 
  add (Strict r) sr = sr {trs = singleton (fromPair r) `union` trs sr}
  add (Weak _)   sr = sr

