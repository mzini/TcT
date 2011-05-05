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

{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE TypeOperators #-}
module Tct.Method.Matrix.NaturalMI where

import Control.Monad (liftM)
import Data.Typeable
import Prelude hiding ((&&),(||),not)
import Text.PrettyPrint.HughesPJ
import qualified Data.Map as Map
import qualified Data.Set as Set

import Qlogic.Boolean
import Qlogic.Diophantine
import Qlogic.Formula (Formula(..))
import Qlogic.MiniSat
import Qlogic.PropositionalFormula
import Qlogic.Semiring
import qualified Qlogic.Assign as A
import qualified Qlogic.NatSat as N
import qualified Qlogic.SatSolver as SatSolver
import qualified Qlogic.Semiring as SR

import Termlib.Problem (Relation (..))
import Termlib.Utils
import qualified Termlib.FunctionSymbol as F
import qualified Termlib.Problem as Prob
import qualified Termlib.Rule as R
import qualified Termlib.Trs as Trs
import qualified Termlib.Variable as V

import Tct.Certificate (poly, expo, certified, unknown)
import Tct.Encoding.AbstractInterpretation
import Tct.Encoding.Matrix hiding (maxMatrix)
import Tct.Encoding.Natring ()
import Tct.Encoding.UsablePositions
import Tct.Method.Matrix.MatrixInterpretation
import Tct.Processor.Args hiding (unit)
import qualified Tct.Processor.Args as A
import Tct.Processor.Args.Instances
import Tct.Processor.Args.Instances ()
import Tct.Processor.Orderings
import Tct.Processor.PPrint (indent)
import qualified Tct.Processor as P
import Tct.Processor (Answerable(..), Verifiable (..), Answer(..), ComplexityProof)
import qualified Tct.Processor.Standard as S

data NaturalMIKind = Algebraic
                   | Automaton
                   | Unrestricted
                     deriving (Typeable, Bounded, Enum)

instance Show NaturalMIKind where 
    show Algebraic    = "algebraic"
    show Automaton    = "automaton"
    show Unrestricted = "nothing"

data MatrixOrder = MatrixOrder { ordInter :: MatrixInter Int
                               , param    :: MatrixKind
                               , uargs    :: UsablePositions } deriving Show

data NaturalMI = NaturalMI deriving (Typeable, Show)

instance PrettyPrintable MatrixOrder where
    pprint order = (text "The following argument positions are usable:")
                   $+$ indent (pprint (uargs order, signature $ ordInter order))
                   $+$ (text "We have the following" <+> ppknd (param order) <+> text "matrix interpretation:")
                   $+$ pprint (ordInter order)
        where ppknd UnrestrictedMatrix            = text "unrestricted"
              ppknd (TriangularMatrix Nothing)    = text "triangular"
              ppknd (TriangularMatrix (Just n))   = text "triangular" <+> parens (text "at most" <+> int n <+> text "in the main diagonals")
              ppknd (ConstructorBased _ Nothing)  = text "constructor-restricted"
              ppknd (ConstructorBased _ (Just n)) = text "constructor-restricted" <+> parens (text "at most" <+> int n <+> text "in the main diagonals")
              ppknd (EdaMatrix Nothing)           = text "EDA-non-satisfying"
              ppknd (EdaMatrix (Just n))          = text "EDA-non-satisfying and IDA" <> parens (int n) <> text "-non-satisfying"

instance PrettyPrintable (MatrixOrder, Trs.Trs, V.Variables) where
    pprint (order, trs, var) = pprint order $+$ pptrs
        where sig = signature $ ordInter order
              pptrs = text "Interpretations of rules:" $+$ vcat (map pprule $ Trs.rules trs)
              pprule r = (text "Rule" <+> pprint (r, sig, var) <+> char ':') $+$ ppterm (R.lhs r) $+$ ppterm (R.rhs r)
              ppterm t = pprint (t, sig, var) <+> char '=' <+> pprint ((interpretTerm (ordInter order) t), var)

instance Answerable MatrixOrder where
    answer (MatrixOrder _ UnrestrictedMatrix _)      = CertAnswer $ certified (unknown, expo (Just 1))
    answer (MatrixOrder m (TriangularMatrix _) _)    = CertAnswer $ certified (unknown, poly (Just (diagonalNonZeroes $ maxNonIdMatrix m)))
    answer (MatrixOrder m (ConstructorBased cs _) _) = CertAnswer $ certified (unknown, poly (Just (diagonalNonZeroes $ maxNonIdMatrix m')))
        where m'       = m{interpretations = filterCs $ interpretations m}
              filterCs = Map.filterWithKey (\f _ -> f `Set.member` cs)
    answer (MatrixOrder m (EdaMatrix Nothing) _)     = CertAnswer $ certified (unknown, poly (Just $ dimension m))
    answer (MatrixOrder _ (EdaMatrix (Just n)) _)    = CertAnswer $ certified (unknown, poly (Just n))

instance Verifiable MatrixOrder
instance ComplexityProof MatrixOrder

instance S.Processor NaturalMI where
    name NaturalMI = "matrix"

    description NaturalMI = [ "This processor orients the problem using matrix-interpretation over natural numbers." ]

    type S.ArgumentsOf NaturalMI = (Arg (EnumOf NaturalMIKind)) :+: (Arg (Maybe Nat)) :+: (Arg Nat) :+: (Arg Nat)  :+: (Arg (Maybe Nat))  :+: (Arg (Maybe Nat)) :+: (Arg Bool)
    arguments NaturalMI = opt { A.name        = "cert"
                              , A.description = unlines [ "This argument specifies restrictions on the matrix-interpretation which induce polynomial growth of"
                                                        , "the interpretation of the considered starting terms relative to their size."
                                                        , "Here 'algebraic' refers to simple algebraic restrictions on matrices (in the current implementation,"
                                                        , "they are simply restricted to triangular shape, i.e. matrices where coefficients in the lower-left"
                                                        , "half below the diagonal are zero. Such matrix-interpretations induce polynomial derivational-complexity." 
                                                        , "If 'automaton' is given as argument, then criteria from the theory of weighted automata are used instead"
                                                        , "(in the current implementation, the negations of the criteria EDA, and possibly IDA(n), in the case that"
                                                        , "the flag 'degree' is set, are used)."
                                                        , "If 'nothing' is given, then matrix-interpretations of all function symbols are unrestricted."
                                                        , "Note that matrix interpretations produced with this option do not induce polynomial complexities in general."
                                                        , "The default value is 'automaton'."
                                                        ]
                              , A.defaultValue = Automaton}
                          :+:
                          opt { A.name        = "degree"
                              , A.description = unlines [ "This argument ensures that the complexity induced by the searched matrix interpretation is bounded by a"
                                                        , "polynomial of the given degree. Its internal effect is dictated by the value the argument 'cert' is set to."
                                                        , "If it is set to 'algebraic', this restricts the number of non-zero entries in the diagonals of the matrices."
                                                        , "If it is set to 'automaton', this set the paramter 'n' in the criterion 'not IDA(n)'."
                                                        , "Finally, if it is set to 'unrestricted', the effect of setting the 'degree' argument is unspecified."
                                                        ]
                              , A.defaultValue = Nothing}
                          :+:
                          opt { A.name        = "dim"
                              , A.description = unlines [ "This argument specifies the dimension of the vectors and square-matrices appearing"
                                                        , " in the matrix-interpretation."]
                              , A.defaultValue = Nat 2 }
                          :+:
                          opt { A.name        = "bound"
                              , A.description = unlines [ "This argument specifies an upper-bound on coefficients appearing in the interpretation."
                                                        , "Such an upper-bound is necessary as we employ bit-blasting to SAT internally"
                                                        , "when searching for compatible matrix interpretations."]
                              , A.defaultValue = Nat 3 }
                          :+:
                          opt { A.name        = "bits"
                              , A.description = unlines [ "This argument plays the same role as 'bound',"
                                                        , "but instead of an upper-bound the number of bits is specified."
                                                        , "This argument overrides the argument 'bound'."]
                              , A.defaultValue = Nothing }
                          :+:
                          opt { A.name = "cbits"
                              , A.description = unlines [ "This argument specifies the number of bits used for intermediate results, "
                                                        , "as for instance coefficients of matrices obtained by interpreting"
                                                        , "left- and right-hand sides."]
                              , A.defaultValue = Nothing }
                          :+:
                          opt { A.name = "uargs"
                              , A.description = unlines [ "This argument specifies whether usable arguments are computed (if applicable)"
                                                        , "in order to relax the monotonicity constraints on the interpretation."]
                              , A.defaultValue = True }
--                           :+:
--                           opt { A.name = "uargs"
--                               , A.description = unlines [ "This argument specifies the approximation used for calculating the usable argument positions."
--                                                         , "Here 'byFunctions' refers to just looking at defined function symbols, while 'byCap' refers"
--                                                         , "to using a tcap-like function." ]
--                               , A.defaultValue = UArgByCap }

    instanceName inst = "matrix-interpretation of dimension " ++ show (dim $ S.processorArgs inst)

    type S.ProofOf NaturalMI = OrientationProof MatrixOrder

    solve inst problem = case Prob.relation problem of
                           Standard sr    -> orientDirect strat st sr sig' (S.processorArgs inst)
                           Relative sr wr -> orientRelative strat st sr wr sig' (S.processorArgs inst)
                           DP sr wr       -> orientDp strat st sr wr sig' (S.processorArgs inst)
        where sig   = Prob.signature problem
              sig'  = sig `F.restrictToSymbols` Trs.functionSymbols (Prob.strictTrs problem `Trs.union` Prob.weakTrs problem)
              st    = Prob.startTerms problem
              strat = Prob.strategy problem

    solvePartial inst problem = case Prob.relation problem of
                                   Standard sr    -> mkProof sr `liftM` orientPartial strat st sr sig' (S.processorArgs inst)
                                   Relative sr wr -> mkProof sr `liftM` orientPartialRelative strat st sr wr sig' (S.processorArgs inst)
                                   DP       _  _  -> return $ P.PartialProof { P.ppInputProblem = problem
                                                                             , P.ppResult       = Inapplicable "Relative Rule Removal inapplicable for DP problems"
                                                                             , P.ppRemovable    = [] }
      where sig   = Prob.signature problem
            sig'  = sig `F.restrictToSymbols` Trs.functionSymbols (Prob.strictTrs problem `Trs.union` Prob.weakTrs problem)
            st    = Prob.startTerms problem
            strat = Prob.strategy problem
            mkProof sr res@(Order (MatrixOrder mi _ _)) = P.PartialProof { P.ppInputProblem = problem
                                                                         , P.ppResult       = res 
                                                                         , P.ppRemovable    = Trs.toRules $ strictRules mi sr}
            mkProof _  res                              = P.PartialProof { P.ppInputProblem = problem
                                                                         , P.ppResult       = res
                                                                         , P.ppRemovable    = [] }

matrixProcessor :: S.StdProcessor NaturalMI
matrixProcessor = S.StdProcessor NaturalMI

matrix :: NaturalMIKind -> Maybe Nat -> Nat -> N.Size -> Maybe Nat -> Bool -> P.InstanceOf (S.StdProcessor NaturalMI)
matrix matrixkind deg matrixdimension coefficientsize constraintbits ua =
    S.StdProcessor NaturalMI `S.withArgs` (matrixkind :+: deg :+: matrixdimension :+: Nat (N.bound coefficientsize) :+: Nothing :+: constraintbits :+: ua)

-- argument accessors

kind :: Domains (S.ArgumentsOf NaturalMI) -> Prob.StartTerms -> MatrixKind
kind (Unrestricted :+: _ :+: _ :+: _ :+: _ :+: _ :+: _) _                      = UnrestrictedMatrix
kind (Algebraic    :+: d :+: _ :+: _ :+: _ :+: _ :+: _) (Prob.BasicTerms _ cs) = ConstructorBased cs (fmap (\ (Nat n) -> n) d)
kind (Algebraic    :+: d :+: _ :+: _ :+: _ :+: _ :+: _) Prob.TermAlgebra       = TriangularMatrix (fmap (\ (Nat n) -> n) d)
kind (Automaton    :+: d :+: _ :+: _ :+: _ :+: _ :+: _) (Prob.BasicTerms _ _)  = EdaMatrix (fmap (\ (Nat n) -> n) d)
kind (Automaton    :+: d :+: _ :+: _ :+: _ :+: _ :+: _) Prob.TermAlgebra       = EdaMatrix (fmap (\ (Nat n) -> n) d)

bound :: Domains (S.ArgumentsOf NaturalMI) -> N.Size
bound (_ :+: _ :+: _ :+: Nat bnd :+: mbits :+: _ :+: _) = case mbits of
                                                            Just (Nat b) -> N.Bits b
                                                            Nothing      -> N.Bound bnd

cbits :: Domains (S.ArgumentsOf NaturalMI) -> Maybe N.Size
cbits (_ :+: _ :+: _ :+: _ :+: _ :+: b :+: _) = do Nat n <- b
                                                   return $ N.Bits n

dim :: Domains (S.ArgumentsOf NaturalMI) -> Int
dim (_ :+: _ :+: Nat d :+: _ :+: _ :+: _ :+: _) = d

isUargsOn :: Domains (S.ArgumentsOf NaturalMI) -> Bool
isUargsOn (_ :+: _ :+: _ :+: _ :+: _ :+: _ :+: ua) = ua

usableArgsWhereApplicable :: MatrixDP -> F.Signature -> Prob.StartTerms -> Bool -> Prob.Strategy -> Trs.Trs -> Trs.Trs -> UsablePositions
usableArgsWhereApplicable MWithDP sig _                     ua strat r s = (if ua then restrictToSignature compSig (usableArgs strat r s) else fullWithSignature compSig) `union` emptyWithSignature nonCompSig
  where compSig    = F.restrictToSymbols sig $ Set.filter (F.isCompound sig) $ F.symbols sig
        nonCompSig = F.restrictToSymbols sig $ Set.filter (not . F.isCompound sig) $ F.symbols sig
usableArgsWhereApplicable MNoDP   sig Prob.TermAlgebra      _  _     _ _ = fullWithSignature sig
usableArgsWhereApplicable MNoDP   sig (Prob.BasicTerms _ _) ua strat r s = if ua then usableArgs strat r s else fullWithSignature sig

-- uastrat :: Domains (S.ArgumentsOf NaturalMI) -> UArgStrategy
-- uastrat (_ :+: _ :+: _ :+: _ :+: _ :+: uas) = uas

orientDirect :: P.SolverM m => Prob.Strategy -> Prob.StartTerms -> Trs.Trs -> F.Signature -> Domains (S.ArgumentsOf NaturalMI) -> m (S.ProofOf NaturalMI)
orientDirect strat st trs sig mp = orientMatrix relativeConstraints ua st trs Trs.empty sig mp
  where ua = usableArgsWhereApplicable MNoDP sig st (isUargsOn mp) strat Trs.empty trs

orientRelative :: P.SolverM m => Prob.Strategy -> Prob.StartTerms -> Trs.Trs -> Trs.Trs -> F.Signature -> Domains (S.ArgumentsOf NaturalMI) -> m (S.ProofOf NaturalMI)
orientRelative strat st strict weak sig mp = orientMatrix relativeConstraints ua st strict weak sig mp
  where ua = usableArgsWhereApplicable MNoDP sig st (isUargsOn mp) strat Trs.empty (strict `Trs.union` weak)

orientDp :: P.SolverM m => Prob.Strategy -> Prob.StartTerms -> Trs.Trs -> Trs.Trs -> F.Signature -> Domains (S.ArgumentsOf NaturalMI) -> m (S.ProofOf NaturalMI)
orientDp strat st strict weak sig mp = orientMatrix dpConstraints ua st strict weak sig mp
  where ua = usableArgsWhereApplicable MWithDP sig st (isUargsOn mp) strat Trs.empty (strict `Trs.union` weak)

orientPartial :: P.SolverM m => Prob.Strategy -> Prob.StartTerms -> Trs.Trs -> F.Signature -> Domains (S.ArgumentsOf NaturalMI) -> m (S.ProofOf NaturalMI)
orientPartial strat st trs sig mp = orientMatrix partialConstraints ua st trs Trs.empty sig mp
  where ua = usableArgsWhereApplicable MNoDP sig st (isUargsOn mp) strat Trs.empty trs

orientPartialRelative :: P.SolverM m => Prob.Strategy -> Prob.StartTerms -> Trs.Trs -> Trs.Trs -> F.Signature -> Domains (S.ArgumentsOf NaturalMI) -> m (S.ProofOf NaturalMI)
orientPartialRelative strat st strict weak sig mp = orientMatrix partialConstraints ua st strict weak sig mp
  where ua = usableArgsWhereApplicable MNoDP sig st (isUargsOn mp) strat Trs.empty (strict `Trs.union` weak)

orientMatrix :: P.SolverM m => (UsablePositions -> Prob.StartTerms -> Trs.Trs -> Trs.Trs -> F.Signature -> Domains (S.ArgumentsOf NaturalMI) -> DioFormula MiniSatLiteral DioVar Int)
             -> UsablePositions -> Prob.StartTerms -> Trs.Trs -> Trs.Trs -> F.Signature -> Domains (S.ArgumentsOf NaturalMI) -> m (S.ProofOf NaturalMI)
orientMatrix f ua st dps trs sig mp = do theMI <- P.minisatValue addAct mi
                                         return $ case theMI of
                                                   Nothing -> Incompatible -- useful for debug: Order $ MatrixOrder (MI 1 sig Map.empty) mk ua
                                                   Just mv -> Order $ MatrixOrder (fmap (\x -> x n) mv) mk ua
                                      where addAct :: MiniSat ()
                                            addAct  = toFormula (liftM N.bound cb) (N.bound n) (f ua st dps trs sig mp) >>= SatSolver.addFormula
                                            mi      = abstractInterpretation mk d sig :: MatrixInter (N.Size -> Int)
                                            n       = bound mp
                                            cb      = cbits mp
                                            d       = dim mp
                                            mk      = kind mp st

data MatrixDP = MWithDP | MNoDP deriving Show
data MatrixRelativity = MDirect | MRelative deriving Show

partialConstraints :: Eq l => UsablePositions -> Prob.StartTerms -> Trs.Trs -> Trs.Trs -> F.Signature -> Domains (S.ArgumentsOf NaturalMI) -> DioFormula l DioVar Int
partialConstraints = matrixConstraints MRelative MNoDP

relativeConstraints :: Eq l => UsablePositions -> Prob.StartTerms -> Trs.Trs -> Trs.Trs -> F.Signature -> Domains (S.ArgumentsOf NaturalMI) -> DioFormula l DioVar Int
relativeConstraints = matrixConstraints MDirect MNoDP

dpConstraints :: Eq l => UsablePositions -> Prob.StartTerms -> Trs.Trs -> Trs.Trs -> F.Signature -> Domains (S.ArgumentsOf NaturalMI) -> DioFormula l DioVar Int
dpConstraints = matrixConstraints MDirect MWithDP

-- TODO: rename derivationGraph
-- weightGapConstraints :: Eq l => Prob.StartTerms -> Trs.Trs -> Trs.Trs -> F.Signature -> S.TheProcessor NaturalMI -> DioFormula l DioVar Int
-- weightGapConstraints = matrixConstraints MWeightGap MNoDP

matrixConstraints :: Eq l => MatrixRelativity -> MatrixDP -> UsablePositions -> Prob.StartTerms -> Trs.Trs -> Trs.Trs -> F.Signature
                  -> Domains (S.ArgumentsOf NaturalMI) -> DioFormula l DioVar Int
matrixConstraints mrel mdp ua st strict weak sig mp = strictChoice mrel absmi strict && weakTrsConstraints absmi weak && dpChoice mdp st uaOn absmi && otherConstraints mk absmi
  where absmi      = abstractInterpretation mk d sig :: MatrixInter (DioPoly DioVar Int)
        d          = dim mp
        mk         = kind mp st
        uaOn       = isUargsOn mp
        otherConstraints UnrestrictedMatrix _              = top
        otherConstraints (TriangularMatrix Nothing) mi     = triConstraints mi
        otherConstraints (TriangularMatrix (Just _)) _     = error "Triangular matrices with restricted number of ones in the main diagonal not yet implemented"
        otherConstraints (ConstructorBased cs Nothing) mi  = triConstraints mi'
                                                             where mi' = mi{interpretations = filterCs $ interpretations mi}
                                                                   filterCs = Map.filterWithKey (\f _ -> f `Set.member` cs)
        otherConstraints (ConstructorBased _ (Just _)) _   = error "Triangular matrices with restricted number of ones in the main diagonal not yet implemented"
        otherConstraints (EdaMatrix Nothing) mi            = edaConstraints mi
        otherConstraints (EdaMatrix (Just deg)) mi         = idaConstraints deg mi
        strictChoice MDirect    = strictTrsConstraints
        strictChoice MRelative  = relativeStricterTrsConstraints
--         strictChoice MWeightGap = strictOneConstraints
        dpChoice MWithDP _                     u     = safeRedpairConstraints sig ua u
        dpChoice MNoDP   Prob.TermAlgebra      _     = monotoneConstraints
        dpChoice MNoDP   (Prob.BasicTerms _ _) True  = uargMonotoneConstraints ua
        dpChoice MNoDP   (Prob.BasicTerms _ _) False = monotoneConstraints

uargMonotoneConstraints :: AbstrOrdSemiring a b => UsablePositions -> MatrixInter a -> b
uargMonotoneConstraints uarg = bigAnd . Map.mapWithKey funConstraint . interpretations
  where funConstraint f = bigAnd . Map.map ((.>=. SR.one) . entry 1 1) . filterUargs f . coefficients
        filterUargs f = Map.filterWithKey $ fun f
        fun f (V.Canon i) _ = isUsable f i uarg
        fun _ (V.User _)  _ = error "Tct.Method.Matrix.NaturalMI.uargMonotoneConstraints: User variable in abstract interpretation"

monotoneConstraints :: AbstrOrdSemiring a b => MatrixInter a -> b
monotoneConstraints = bigAnd . Map.map (bigAnd . Map.map ((.>=. SR.one) . entry 1 1) . coefficients) . interpretations

safeRedpairConstraints :: AbstrOrdSemiring a b => F.Signature -> UsablePositions -> Bool -> MatrixInter a -> b
safeRedpairConstraints sig uarg uaOn = bigAnd . Map.mapWithKey funConstraint . compInterpretations
                                       where compInterpretations = Map.filterWithKey isCompound . interpretations
                                             isCompound f _      = F.isCompound sig f
                                             funConstraint f     = bigAnd . Map.map ((.>=. SR.one) . entry 1 1) . filterUargs f . coefficients
                                             filterUargs f xs    = if uaOn then Map.filterWithKey (fun f) xs else xs
                                             fun f (V.Canon i) _ = isUsable f i uarg
                                             fun _ (V.User _)  _ = error "Tct.Method.Matrix.NaturalMI.safeRedPairConstraints: User variable in abstract interpretation"

slmiSafeRedpairConstraints :: (MIEntry a, AbstrOrdSemiring a b) => F.Signature -> UsablePositions -> MatrixInter a -> b
slmiSafeRedpairConstraints sig uarg mi = bigAnd $ Map.mapWithKey funConstraint $ compInterpretations mi
                                         where compInterpretations = Map.filterWithKey isCompound . interpretations
                                               isCompound f _      = F.isCompound sig f
                                               d                   = dimension mi
                                               funConstraint f     = bigAnd . Map.map (.==. unit d) . filterUargs f . coefficients
                                               filterUargs f       = Map.filterWithKey $ fun f
                                               fun f (V.Canon i) _ = isUsable f i uarg
                                               fun _ (V.User _)  _ = error "Tct.Method.Matrix.NaturalMI.slmiSafeRedPairConstraints: User variable in abstract interpretation"

positiveConstraints :: AbstrOrdSemiring a b => MatrixInter a -> b
positiveConstraints mi = positiveMatrices mi && positiveVectors mi

positiveMatrices :: AbstrOrdSemiring a b => MatrixInter a -> b
positiveMatrices = bigAnd . Map.map (bigAnd . Map.map (liftMatrix (bigAnd . map (liftVector bigAnd)) . fmap (.>=. SR.zero)) . coefficients) . interpretations

positiveVectors :: AbstrOrdSemiring a b => MatrixInter a -> b
positiveVectors = bigAnd . Map.map (liftVector bigAnd . fmap (.>=. SR.zero) . constant) . interpretations

checkDirect :: MatrixInter Int -> Trs.Trs -> Bool
checkDirect mi trs = strictTrsConstraints mi trs && monotoneConstraints mi

strictRules :: MatrixInter Int -> Trs.Trs -> Trs.Trs
strictRules mi = Trs.filterRules $ strictRuleConstraints mi

applyAss :: (Ord l, Eq l) => MatrixInter (N.NatFormula l) -> A.Assign l -> MatrixInter Int
applyAss mi ass = fmap (flip N.eval ass) mi

-- Automaton Stuff
-- Notation follows the 5-author CAI paper

data XdaVar = Ggeq Int Int
            | Ggrt Int Int
            | Gtwo Int Int Int Int
            | R Int Int
            | D Int Int
            | Done Int Int
            | Dtwo Int Int
            | Gthree Int Int Int Int Int Int
            | T Int Int Int
            | I Int Int
            | J Int Int
            | H Int Int -- first Argument: actual argument of h in the paper; second argument: height
            deriving (Eq, Ord, Show, Typeable)

instance PropAtom XdaVar

dioAtom :: (PropAtom a, Eq l) => a -> DioFormula l DioVar Int
dioAtom = A . PAtom . toDioVar

edaConstraints :: Eq l => MatrixInter (DioPoly DioVar Int) -> DioFormula l DioVar Int
edaConstraints mi = goneConstraints mi && gtwoConstraints mi && rConstraints mi && dConstraints mi

idaConstraints :: Eq l => Int -> MatrixInter (DioPoly DioVar Int) -> DioFormula l DioVar Int
idaConstraints deg mi = edaConstraints mi && gThreeConstraints mi && tConstraints mi && iConstraints mi && jConstraints mi && hConstraints deg mi

goneConstraints :: Eq l => MatrixInter (DioPoly DioVar Int) -> DioFormula l DioVar Int
goneConstraints mi = bigAnd [ f i j | i <- toD, j <- toD ]
  where d     = dimension mi
        toD   = [1..d]
        f i j = g i j && h i j
        g i j = (dioAtom $ Ggeq i j) <-> bigOr (map (bigOr . map (\ m -> entry i j m .>=. SR.one) . Map.elems . coefficients) $ Map.elems $ interpretations mi)
        h i j = (dioAtom $ Ggrt i j) <-> bigOr (map (bigOr . map (\ m -> entry i j m .>. SR.one) . Map.elems . coefficients) $ Map.elems $ interpretations mi)

gtwoConstraints :: Eq l => MatrixInter (DioPoly DioVar Int) -> DioFormula l DioVar Int
gtwoConstraints mi  = bigAnd [ f i j k l | i <- toD, j <- toD, k <- toD, l <- toD ]
  where d           = dimension mi
        toD         = [1..d]
        f i j k l   = (dioAtom $ Gtwo i j k l) <-> bigOr (map (bigOr . map (g i j k l) . Map.elems . coefficients) $ Map.elems $ interpretations mi)
        g i j k l m = (entry i k m .>=. SR.one) && (entry j l m .>=. SR.one)

rConstraints :: Eq l => MatrixInter (DioPoly DioVar Int) -> DioFormula l DioVar Int
rConstraints mi = reflexivity && transitivity && compatibility && nocycle
  where d   = dimension mi
        toD = [1..d]
        reflexivity   = bigAnd $ map (\ x -> dioAtom (R x x)) toD
        transitivity  = bigAnd [ (dioAtom (R x y) && dioAtom (R y z)) --> dioAtom (R x z) | x <- toD, y <- toD, z <- toD ]
        compatibility = bigAnd [ dioAtom (Ggeq x y) --> dioAtom (R x y) | x <- toD, y <- toD ]
        nocycle       = bigAnd [ dioAtom (Ggrt x y) --> not (dioAtom (R y x)) | x <- toD, y <- toD ]

dConstraints :: Eq l => MatrixInter (DioPoly DioVar Int) -> DioFormula l DioVar Int
dConstraints mi = diagonal && foreapprox && forecompat && backapprox && backcompat && exactness
  where d           = dimension mi
        toD         = [1..d]
        diagonal    = bigAnd [ if x == y then dioAtom (D x y) else not (dioAtom $ D x y) | x <- toD, y <- toD ]
        foreapprox  = bigAnd [ dioAtom (D x y) --> dioAtom (Done x y) | x <- toD, y <- toD ]
        forecompat  = bigAnd [ (dioAtom (Done x y) && dioAtom (Gtwo x y z u)) --> dioAtom (Done z u) | x <- toD, y <- toD, z <- toD, u <- toD ]
        backapprox = bigAnd [ dioAtom (D x y) --> dioAtom (Dtwo x y) | x <- toD, y <- toD ]
        backcompat = bigAnd [ (dioAtom (Dtwo x y) && dioAtom (Gtwo z u x y)) --> dioAtom (Dtwo z u) | x <- toD, y <- toD, z <- toD, u <- toD ]
        exactness   = bigAnd [ (dioAtom (Done x y) && dioAtom (Dtwo x y)) --> dioAtom (D x y) | x <- toD, y <- toD ]

gThreeConstraints :: Eq l => MatrixInter (DioPoly DioVar Int) -> DioFormula l DioVar Int
gThreeConstraints mi = bigAnd [ f i j k x y z | i <- toD, j <- toD, k <- toD, x <- toD, y <- toD, z <- toD ]
  where d         = dimension mi
        toD       = [1..d]
        f i j k x y z = (dioAtom $ Gthree i j k x y z) <-> bigOr (map (bigOr . map (g i j k x y z) . Map.elems . coefficients) $ Map.elems $ interpretations mi)
        g i j k x y z m = (entry i x m .>=. SR.one) && (entry j y m .>=. SR.one) && (entry k z m .>=. SR.one)

tConstraints :: Eq l => MatrixInter (DioPoly DioVar Int) -> DioFormula l DioVar Int
tConstraints mi = initial && gThreeStep
  where d = dimension mi
        toD = [1..d]
        initial = bigAnd [ if x == y then top else dioAtom (T x x y) | x <- toD, y <- toD ]
        gThreeStep = bigAnd [ (dioAtom (T x y z) && dioAtom (Gthree x y z u v w)) --> dioAtom (T u v w) | x <- toD, y <- toD, z <- toD, u <- toD, v <- toD, w <- toD ]

iConstraints :: Eq l => MatrixInter (DioPoly DioVar Int) -> DioFormula l DioVar Int
iConstraints mi = bigAnd [ if x == y then Top else dioAtom (T x y y) --> dioAtom (I x y) | x <- toD, y <- toD ]
  where d = dimension mi
        toD = [1..d]

jConstraints :: Eq l => MatrixInter (DioPoly DioVar Int) -> DioFormula l DioVar Int
jConstraints mi = bigAnd [ f i j | i <- toD, j <- toD ]
  where d = dimension mi
        toD = [1..d]
        f i j = dioAtom (J i j) <-> bigOr (map (\ k -> dioAtom (I i k) && dioAtom (R k j)) toD)

hConstraints :: Eq l => Int -> MatrixInter (DioPoly DioVar Int) -> DioFormula l DioVar Int
hConstraints deg mi = unaryNotation && jDecrease
  where d = dimension mi
        toD = [1..d]
        unaryNotation = bigAnd [ dioAtom (H x h) --> dioAtom (H x (h - 1)) | x <- toD, h <- [2..deg] ]
        jDecrease = bigAnd [ f i j | i <- toD, j <- toD ]
        f i j = dioAtom (J i j) --> bigOr (map (\ h -> dioAtom (H i h) && not (dioAtom $ H j h)) [1..deg])

-- Instance declarations

class MIEntry a

instance MIEntry Int

instance MIEntry (DioPoly DioVar Int)

instance MIEntry (DioFormula l DioVar Int)

instance MIEntry a => MIEntry (Vector a)

instance (AbstrEq a b, MIEntry a) => AbstrEq (Vector a) b where
  (Vector vs) .==. (Vector ws) = bigAnd $ zipWith (.==.) vs ws

instance (AbstrOrd a b, MIEntry a) => AbstrOrd (Vector a) b where
  (Vector [])     .<. _               = bot
  _               .<. (Vector [])     = bot
  (Vector (v:vs)) .<. (Vector (w:ws)) = (v .<. w) && (Vector vs .<=. Vector ws)
  (Vector vs) .<=. (Vector ws)        = bigAnd $ zipWith (.<=.) vs ws

instance (AbstrEq a b, MIEntry a) => AbstrEq (Matrix a) b where
  (Matrix vs) .==. (Matrix ws) = (Vector vs) .==. (Vector ws)

instance (AbstrOrd a b, MIEntry a) => AbstrOrd (Matrix a) b where
  (Matrix vs) .<. (Matrix ws) = (Vector vs) .<. (Vector ws)
  (Matrix vs) .<=. (Matrix ws) = (Vector vs) .<=. (Vector ws)

instance (AbstrEq a b, MIEntry a) => AbstrEq (LInter a) b where
  (LI lcoeffs lconst) .==. (LI rcoeffs rconst) = bigAnd (Map.elems zipmaps) && lconst .==. rconst
                                                 where zipmaps = Map.intersectionWith (.==.) lcoeffs rcoeffs

instance (AbstrOrd a b, MIEntry a) => AbstrOrd (LInter a) b where
  (LI lcoeffs lconst) .<. (LI rcoeffs rconst) = bigAnd (Map.elems zipmaps) && lconst .<. rconst
                                                where zipmaps = Map.intersectionWith (.<=.) lcoeffs rcoeffs
  (LI lcoeffs lconst) .<=. (LI rcoeffs rconst) = bigAnd (Map.elems zipmaps) && lconst .<=. rconst
                                                 where zipmaps = Map.intersectionWith (.<=.) lcoeffs rcoeffs

instance (Ord l, SatSolver.Solver s l) => MSemiring s l (N.NatFormula l) DioVar Int where
  plus = N.mAdd
  prod = N.mTimes
  zero = N.natToFormula 0
  one  = N.natToFormula 1
  geq  = N.mGeq
  grt  = N.mGrt
  equ  = N.mEqu
  constToFormula = N.natToFormula
  formAtom = N.natAtomM . N.Bound
  truncFormTo = N.mTruncTo

instance SatSolver.Decoder (MatrixInter (N.Size -> Int)) (N.PLVec DioVar) where
  add (N.PLVec (DioVar y) k) mi = case cast y of
                                      Nothing -> mi
                                      Just x -> mi{interpretations = Map.adjust newli fun (interpretations mi)}
                                        where newli li | pos == 0  = li{constant = adjustv newval i (constant li)}
                                              newli li | otherwise = li{coefficients = newli' li}
                                              newli' li    = Map.adjust newm (V.Canon pos) (coefficients li)
                                              newm         = adjustm newval i j
                                              newval old n = old n + (2 ^ ((if r then 1 else N.bits n) - k))
                                              r   = restrict x
                                              fun = varfun x
                                              pos = argpos x
                                              i   = varrow x
                                              j   = varcol x
