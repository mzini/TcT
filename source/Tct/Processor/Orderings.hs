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

module Tct.Processor.Orderings 
    (OrientationProof (..))
where

import Text.PrettyPrint.HughesPJ
import Tct.Certificate (constant, certified)
import Tct.Processor (Answer (..), ComplexityProof(..))
import Tct.Processor.PPrint (indent)

data OrientationProof o = Order o
                        | Incompatible
                        | Empty
                        | Inapplicable String deriving Show

instance ComplexityProof o => ComplexityProof (OrientationProof o) where
    pprintProof Empty            _  = text "All strict components are empty, nothing to further orient"
    pprintProof (Order o)        mde = pprintProof o mde
    pprintProof Incompatible     _   = text "The input cannot be shown compatible"
    pprintProof (Inapplicable s) _   = text "The processor is inapplicable, reason:"
                                       $+$ indent (text s)

    answer (Order o) = answer o
    answer Empty     = CertAnswer $ certified (constant, constant)
    answer Incompatible = MaybeAnswer
    answer (Inapplicable _) = MaybeAnswer
