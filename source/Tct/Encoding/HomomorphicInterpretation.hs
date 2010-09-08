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
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableInstances #-}

module Tct.Encoding.HomomorphicInterpretation where

import Tct.Encoding.AbstractInterpretation
import qualified Termlib.FunctionSymbol as F
import qualified Termlib.Term as T
import qualified Termlib.Variable as V

class Interpretation a c | a -> c where
  interpretFun :: a -> F.Symbol -> [c] -> c
  interpretVar :: a -> V.Variable -> c

instance Interpretation a c => Algebra a c where
  interpretTerm a (T.Var v)    = interpretVar a v
  interpretTerm a (T.Fun f ts) = interpretFun a f ts'
                                 where ts' = map (interpretTerm a) ts
