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

module Tct.Method.Weightgap where

import Prelude hiding ((&&))
import qualified Data.Map as Map
import qualified Data.Set as Set

import Qlogic.Boolean
import Qlogic.Diophantine
import Qlogic.Semiring
import qualified Qlogic.NatSat as N

import qualified Termlib.FunctionSymbol as F
import qualified Termlib.Problem as Prob
import qualified Termlib.Rule as R
import qualified Termlib.Trs as Trs

import Tct.Encoding.AbstractInterpretation
import Tct.Encoding.Matrix
import Tct.Encoding.UsablePositions
import Tct.Processor.Args
import Tct.Processor.Args.Instances
import Tct.Processor.Orderings
import Tct.Method.Matrix.MatrixInterpretation
import Tct.Method.Matrix.NaturalMI
import qualified Tct.Processor as P
import qualified Tct.Processor.Standard as S

applyWeightGap :: P.SolverM m => UsablePositions -> Trs.Trs -> Trs.Trs -> Prob.StartTerms -> F.Signature -> NaturalMIKind -> Nat -> N.Size -> Maybe Nat -> UArgStrategy
               -> m (OrientationProof MatrixOrder)
applyWeightGap uarg nondup trs st sig mk d b cb uas = orientMatrix (weightGapConstraints uarg nondup) st trs Trs.empty sig (mk :+: d :+: (nat $ N.bound b) :+: Nothing :+: cb :+: uas)

weightGapConstraints :: Eq l => UsablePositions -> Trs.Trs -> Prob.StartTerms -> Trs.Trs -> Trs.Trs -> F.Signature -> Domains (S.ArgumentsOf NaturalMI) -> DioFormula l DioVar Int
weightGapConstraints uarg nondup st strict weak sig mp = strictTrsConstraints absmi strict && weakTrsConstraints absmi weak && otherConstraints
  where absmi      = abstractInterpretation mk d sig :: MatrixInter (DioPoly DioVar Int)
        d          = dim mp
        mk         = kind mp st
        otherConstraints = safeRedpairConstraints sig absmi && uargMonotoneConstraints uarg absmi && nondupConstraints nondup absmi && mkConstraints mk absmi
        mkConstraints UnrestrictedMatrix _ = top
        mkConstraints TriangularMatrix mi = triConstraints mi
        mkConstraints (ConstructorBased cs) mi = triConstraints mi'
                                                 where mi' = mi{interpretations = filterCs $ interpretations mi}
                                                       filterCs = Map.filterWithKey (\f _ -> f `Set.member` cs)

nondupConstraints :: (AbstrOrdSemiring a b, MIEntry a) => Trs.Trs -> MatrixInter a -> b
nondupConstraints trs mi = bigAnd $ Trs.liftTrs (map rConstraint) trs
  where rConstraint r = bigAnd $ zipWith coeffConstraint (Map.elems $ coefficients $ interpretTerm mi $ R.lhs r) (Map.elems $ coefficients $ interpretTerm mi $ R.rhs r)
        coeffConstraint lm rm = row 1 lm .>=. row 1 rm
