{-# LANGUAGE TypeFamilies #-}
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

module Tct.Processor.Transformations where

import Tct.Proof 
import Termlib.Problem
import Termlib.Utils (PrettyPrintable (..))
import Text.PrettyPrint.HughesPJ

import qualified Tct.Processor as P
import qualified Tct.Processor.Args as A
import Tct.Processor.Args hiding (name, description, synopsis)


data TransformationProof t subs = TransformationProof { transformationProof :: t
                                                      , subs :: [subs]}

data TheTransformer t = TheTransformer { transformation :: t
                                       , transformationArgs :: Domain (ArgumentsOf t)}

instance Answerable (TransformationProof t subs)


class Transformer t where
    type ArgumentsOf t
    type ProofOf t
    name         :: t -> String
    instanceName :: TheTransformer t -> String
    instanceName = name . transformation
    description  :: t -> [String]
    description  = const []
    arguments    :: t -> (ArgumentsOf t)
    transform    :: P.SolverM m => TheTransformer t -> Problem -> m (TransformationProof t [Problem])


-- data TransformationProof tp sp =  o
--                                | Incompatible
--                                | Inapplicable String

-- instance PrettyPrintable o => PrettyPrintable (OrientationProof o) where
--     pprint (Order o) = pprint o
--     pprint Incompatible = text "The input cannot be shown compatible"
--     pprint (Inapplicable s) = text s

-- instance Answerable o => Answerable (OrientationProof o) where
--     answer (Order o) = answer o
--     answer Incompatible = MaybeAnswer
--     answer (Inapplicable _) = MaybeAnswer

-- instance (PrettyPrintable o, Answerable o) => ComplexityProof (OrientationProof o)
