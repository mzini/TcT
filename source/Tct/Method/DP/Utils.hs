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

module Tct.Method.DP.Utils where

import Text.PrettyPrint.HughesPJ hiding (empty)

import Termlib.Utils

data DPError = NonDPProblemGiven 
             | NonRCProblemGiven
             | NotApplicable Doc
             | ContainsStrictRule

instance PrettyPrintable DPError where 
    pprint NonDPProblemGiven = text "The input problem is not a DP-problem."
    pprint NonRCProblemGiven = text "The input problem is not an RC-problem."
    pprint (NotApplicable r) = hang (text "The processor is not applicable. Reason:") 3 r
    pprint ContainsStrictRule = paragraph "The processor is inapplicable since the strict component of the input problem is not empty"
    
