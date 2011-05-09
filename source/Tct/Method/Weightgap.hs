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

data WeightGap = WeightGap

data WeightGapProof = WeightGapProof

applyWeightGap :: P.SolverM m => Trs.Trs -> UsablePositions -> Trs.Trs -> Prob.StartTerms -> F.Signature -> NaturalMIKind -> Maybe Nat -> Nat -> N.Size -> Maybe Nat -> Bool
               -> m (OrientationProof MatrixOrder)
applyWeightGap nondup uarg trs st sig mk deg d b cb ua = orientMatrix (weightGapConstraints nondup) uarg' st trs Trs.empty sig (mk :+: deg :+: d :+: (Nat $ N.bound b) :+: Nothing :+: cb :+: ua)
  where uarg' = if ua then uarg else fullWithSignature sig

weightGapConstraints :: Eq l => Trs.Trs -> UsablePositions -> Prob.StartTerms -> Trs.Trs -> Trs.Trs -> F.Signature -> Domains (S.ArgumentsOf NaturalMI) -> DioFormula l DioVar Int
weightGapConstraints nondup uarg st strict weak sig mp = strictTrsConstraints absmi strict && weakTrsConstraints absmi weak && otherConstraints
  where absmi      = abstractInterpretation mk d sig :: MatrixInter (DioPoly DioVar Int)
        d          = dim mp
        mk         = kind mp st
        otherConstraints = slmiSafeRedpairConstraints sig uarg absmi && uargMonotoneConstraints uarg absmi && nondupConstraints nondup absmi && mkConstraints mk absmi
        mkConstraints UnrestrictedMatrix _ = top
        mkConstraints (TriangularMatrix Nothing) mi = triConstraints mi
        mkConstraints (TriangularMatrix (Just deg)) mi = triConstraints mi && diagOnesConstraints deg mi
        mkConstraints (ConstructorBased cs Nothing) mi = triConstraints mi'
                                                         where mi' = mi{interpretations = filterCs $ interpretations mi}
                                                               filterCs = Map.filterWithKey (\f _ -> f `Set.member` cs)
        mkConstraints (ConstructorBased cs (Just deg)) mi = triConstraints mi' && diagOnesConstraints deg mi'
                                                            where mi' = mi{interpretations = filterCs $ interpretations mi}
                                                                  filterCs = Map.filterWithKey (\f _ -> f `Set.member` cs)
        mkConstraints (EdaMatrix Nothing) mi = edaConstraints mi
        mkConstraints (EdaMatrix (Just deg)) mi = idaConstraints deg mi

nondupConstraints :: (AbstrOrdSemiring a b, MIEntry a) => Trs.Trs -> MatrixInter a -> b
nondupConstraints trs mi = bigAnd $ Trs.liftTrs (map rConstraint) trs
  where rConstraint r = bigAnd $ zipWith coeffConstraint (Map.elems $ coefficients $ interpretTerm mi $ R.lhs r) (Map.elems $ coefficients $ interpretTerm mi $ R.rhs r)
        coeffConstraint lm rm = row 1 lm .>=. row 1 rm
