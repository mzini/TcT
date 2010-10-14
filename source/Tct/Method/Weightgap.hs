module Tct.Method.Weightgap where

import Prelude hiding ((&&))
import qualified Data.Map as Map
import qualified Data.Set as Set

import Qlogic.Boolean
import Qlogic.Diophantine
import Qlogic.Semiring
import qualified Qlogic.NatSat as N
import qualified Qlogic.Semiring as SR

import qualified Termlib.FunctionSymbol as F
import qualified Termlib.Problem as Prob
import qualified Termlib.Rule as R
import qualified Termlib.Trs as Trs
import qualified Termlib.Variable as V

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

applyWeightGap :: P.SolverM m => UsablePositions -> Trs.Trs -> Trs.Trs -> Prob.StartTerms -> F.Signature -> NaturalMIKind -> Nat -> N.Size -> Maybe Nat -> m (OrientationProof MatrixOrder)
applyWeightGap uarg dps trs st sig mk d b cb 
    | Trs.isDuplicating dps = return $ Inapplicable "duplicating"
    | otherwise             = orientMatrix (weightGapConstraints uarg dps) st trs Trs.empty sig (mk :+: d :+: (nat $ N.bound b) :+: Nothing :+: cb)

weightGapConstraints :: Eq l => UsablePositions -> Trs.Trs -> Prob.StartTerms -> Trs.Trs -> Trs.Trs -> F.Signature -> Domains (S.ArgumentsOf NaturalMI) -> DioFormula l DioVar Int
weightGapConstraints uarg nondup st strict weak sig mp = strictTrsConstraints absmi strict && weakTrsConstraints absmi weak && otherConstraints
  where absmi      = abstractInterpretation mk d (sig `F.restrictToSymbols` Trs.functionSymbols (strict `Trs.union` weak)) :: MatrixInter (DioPoly DioVar Int)
        d          = dim mp
        mk         = kind mp st
        otherConstraints = safeRedpairConstraints sig absmi && uargMonotoneConstraints uarg absmi && nondupConstraints nondup absmi && mkConstraints mk absmi
        mkConstraints UnrestrictedMatrix _ = top
        mkConstraints TriangularMatrix mi = triConstraints mi
        mkConstraints (ConstructorBased cs) mi = triConstraints mi'
                                                 where mi' = mi{interpretations = filterCs $ interpretations mi}
                                                       filterCs = Map.filterWithKey (\f _ -> f `Set.member` cs)

uargMonotoneConstraints :: AbstrOrdSemiring a b => UsablePositions -> MatrixInter a -> b
uargMonotoneConstraints uarg = bigAnd . Map.mapWithKey funConstraint . interpretations
  where funConstraint f = bigAnd . Map.map ((.>=. SR.one) . entry 1 1) . filterUargs f . coefficients
        filterUargs f = Map.filterWithKey $ fun f
        fun f (V.Canon i) _ = isUsable f i uarg
        fun _ (V.User _) _ = error "Tct.Method.Weightgap.uargMonotoneConstraints: User variable in abstract interpretation"

nondupConstraints :: (AbstrOrdSemiring a b, MIEntry a) => Trs.Trs -> MatrixInter a -> b
nondupConstraints trs mi = bigAnd $ Trs.liftTrs (map rConstraint) trs
  where rConstraint r = bigAnd $ zipWith coeffConstraint (Map.elems $ coefficients $ interpretTerm mi $ R.lhs r) (Map.elems $ coefficients $ interpretTerm mi $ R.rhs r)
        coeffConstraint lm rm = row 1 lm .>=. row 1 rm
