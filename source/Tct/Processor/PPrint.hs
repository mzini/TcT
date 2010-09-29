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

module Tct.Processor.PPrint where

import Text.PrettyPrint.HughesPJ
import Termlib.Utils (($++$), PrettyPrintable (..), underline, enumerated, pprintInt)

heading :: String -> Doc
heading n = underline (text $ n ++ ":")

enum :: (PrettyPrintable t) => [t] -> Doc
enum ps = enumerated [pprintInt i | i <- [1..]] [pprint p $+$ text "" | p <- ps]

overview :: (PrettyPrintable t) => [t] -> Doc
overview [] = empty
overview [d] = heading "Overview" $+$ (nest 2 $ pprint d)
overview ds = heading "Overview" $+$ (nest 2 $ enum ds)

details :: (PrettyPrintable t) => [t] -> Doc
details [] = empty
details [d] = heading "Details" $+$ (nest 2 $ pprint d)
details ds = heading "Details" $+$ (nest 2 $ enum ds)

