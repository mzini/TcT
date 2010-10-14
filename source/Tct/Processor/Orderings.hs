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

module Tct.Processor.Orderings where

import Tct.Proof 
import Termlib.Utils (PrettyPrintable (..))
import Text.PrettyPrint.HughesPJ

data OrientationProof o = Order o
                        | Incompatible
                        | Inapplicable String deriving Show

instance PrettyPrintable o => PrettyPrintable (OrientationProof o) where
    pprint (Order o) = pprint o
    pprint Incompatible = text "The input cannot be shown compatible"
    pprint (Inapplicable s) = text s

instance Answerable o => Answerable (OrientationProof o) where
    answer (Order o) = answer o
    answer Incompatible = MaybeAnswer
    answer (Inapplicable _) = MaybeAnswer