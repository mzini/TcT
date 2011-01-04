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
import Qlogic.MiniSat
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
import Tct.Processor.Args
import qualified Tct.Processor.Args as A
import Tct.Processor.Args.Instances
import Tct.Processor.Args.Instances ()
import Tct.Processor.Orderings
import Tct.Processor.PartialProcessor
import Tct.Processor.PPrint (indent)
import Tct.Proof
import qualified Tct.Processor as P
import qualified Tct.Processor.Standard as S

data NaturalMIKind = Triangular
                   | Constructor
                   | Unrestricted
                   | Default
                     deriving (Typeable, Bounded, Enum)

instance Show NaturalMIKind where 
    show Unrestricted = "unrestricted"
    show Triangular   = "triangular"
    show Constructor  = "constructor"
    show Default      = "default"

data MatrixOrder = MatrixOrder { ordInter :: MatrixInter Int
                               , param    :: MatrixKind
                               , uargs    :: UsablePositions } deriving Show

data NaturalMI = NaturalMI deriving (Typeable, Show)

instance PrettyPrintable MatrixOrder where
    pprint order = (text "The following argument positions are usable:")
                   $+$ indent (pprint (uargs order, signature $ ordInter order))
                   $+$ (text "We have the following" <+> ppknd (param order) <+> text "matrix interpretation:")
                   $+$ pprint (ordInter order)
        where ppknd UnrestrictedMatrix   = text "unrestricted"
              ppknd TriangularMatrix     = text "triangular"
              ppknd (ConstructorBased _) = text "constructor-restricted"

instance PrettyPrintable (MatrixOrder, Trs.Trs, V.Variables) where
    pprint (order, trs, var) = pprint order $+$ pptrs
        where sig = signature $ ordInter order
              pptrs = text "Interpretations of rules:" $+$ vcat (map pprule $ Trs.rules trs)
              pprule r = (text "Rule" <+> pprint (r, sig, var) <+> char ':') $+$ ppterm (R.lhs r) $+$ ppterm (R.rhs r)
              ppterm t = pprint (t, sig, var) <+> char '=' <+> pprint ((interpretTerm (ordInter order) t), var)

instance Answerable MatrixOrder where
    answer (MatrixOrder _ UnrestrictedMatrix _)    = CertAnswer $ certified (unknown, expo (Just 1))
    answer (MatrixOrder m TriangularMatrix _)      = CertAnswer $ certified (unknown, poly (Just (diagonalNonZeroes $ maxNonIdMatrix m)))
    answer (MatrixOrder m (ConstructorBased cs) _) = CertAnswer $ certified (unknown, poly (Just (diagonalNonZeroes $ maxNonIdMatrix m')))
        where m'       = m{interpretations = filterCs $ interpretations m}
              filterCs = Map.filterWithKey (\f _ -> f `Set.member` cs)

instance ComplexityProof MatrixOrder

instance S.Processor NaturalMI where
    name NaturalMI = "matrix"

    description NaturalMI = [ "This processor orients the problem using matrix-interpretation over natural numbers." ]

    type S.ArgumentsOf NaturalMI = (Arg (EnumOf NaturalMIKind)) :+: (Arg Nat) :+: (Arg Nat)  :+: (Arg (Maybe Nat))  :+: (Arg (Maybe Nat)) :+: (Arg Bool)
    arguments NaturalMI = opt { A.name        = "kind"
                              , A.description = unlines [ "This argument specifies the particular shape of the matrix-interpretation employed for complexity-analysis."
                                                        , "Here 'triangular' refers to matrices of triangular shape, i.e. matrices where coefficients in the lower-left half below the"
                                                        , "diagonal are zero. Such matrix-interpretations induce polynomial derivational-complexity." 
                                                        , "If 'constructor' is given as argument, then defined symbols are interpreted using unrestricted"
                                                        , "matrix-interpretations, whereas constructors are interpreted by interpretations of triangular shape."
                                                        , "Such matrix-interpretations induce polynomial upper-bounds on the runtime-complexity."
                                                        , "If 'unrestricted' is given, then matrix-interpretations of all function symbols are unrestricted."
                                                        , "Those induce exponentially bounded derivational-complexity."
                                                        , "Finally 'default' is 'constructor' for runtime-, and 'triangular' for derivational-complexity analysis."
                                                        ]
                              , A.defaultValue = Default}
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

instance PartialProcessor NaturalMI where
  solvePartial inst problem = case Prob.relation problem of
                                Standard sr    -> do res <- orientPartial strat st sr sig' (S.processorArgs inst)
                                                     case res of
                                                       Order (MatrixOrder mi _ _) -> do let ppstr = strictRules mi sr
                                                                                        return $ PartialProof problem res ppstr
                                                       _                          -> return $ PartialProof problem res Trs.empty
                                Relative sr wr -> do res <- orientPartialRelative strat st sr wr sig' (S.processorArgs inst)
                                                     case res of
                                                       Order (MatrixOrder mi _ _) -> do let ppstr = strictRules mi sr
                                                                                        return $ PartialProof problem res ppstr
                                                       _                          -> return $ PartialProof problem res Trs.empty
                                DP       _  _  -> return $ PartialProof problem (Inapplicable "Relative Rule Removal inapplicable for DP problems") Trs.empty
      where sig   = Prob.signature problem
            sig'  = sig `F.restrictToSymbols` Trs.functionSymbols (Prob.strictTrs problem `Trs.union` Prob.weakTrs problem)
            st    = Prob.startTerms problem
            strat = Prob.strategy problem

matrixProcessor :: S.StdProcessor NaturalMI
matrixProcessor = S.StdProcessor NaturalMI

matrixPartialProcessor :: S.StdProcessor (ChoiceProc NaturalMI P.AnyProcessor)
matrixPartialProcessor = S.StdProcessor $ ChoiceProc NaturalMI

matrix :: NaturalMIKind -> Nat -> N.Size -> Maybe Nat -> Bool -> P.InstanceOf (S.StdProcessor NaturalMI)
matrix matrixkind matrixdimension coefficientsize constraintbits ua =
    NaturalMI `S.withArgs` (matrixkind :+: matrixdimension :+: Nat (N.bound coefficientsize) :+: Nothing :+: constraintbits :+: ua)

-- argument accessors

kind :: Domains (S.ArgumentsOf NaturalMI) -> Prob.StartTerms -> MatrixKind
kind (Unrestricted :+: _ :+: _ :+: _ :+: _ :+: _) _                      = UnrestrictedMatrix
kind (Constructor  :+: _ :+: _ :+: _ :+: _ :+: _) (Prob.BasicTerms _ cs) = ConstructorBased cs
kind (Constructor  :+: _ :+: _ :+: _ :+: _ :+: _) Prob.TermAlgebra       = error "Constructor based matrix interpretations inapplicable for derivational complexity"
kind (Default      :+: _ :+: _ :+: _ :+: _ :+: _) (Prob.BasicTerms _ cs) = ConstructorBased cs
kind (Default      :+: _ :+: _ :+: _ :+: _ :+: _) Prob.TermAlgebra       = TriangularMatrix
kind (Triangular   :+: _ :+: _ :+: _ :+: _ :+: _) _                      = TriangularMatrix

bound :: Domains (S.ArgumentsOf NaturalMI) -> N.Size
bound (_ :+: _ :+: Nat bnd :+: mbits :+: _ :+: _) = case mbits of
                                                      Just (Nat b) -> N.Bits b
                                                      Nothing      -> N.Bound bnd

cbits :: Domains (S.ArgumentsOf NaturalMI) -> Maybe N.Size
cbits (_ :+: _ :+: _ :+: _ :+: b :+: _) = do Nat n <- b
                                             return $ N.Bits n

dim :: Domains (S.ArgumentsOf NaturalMI) -> Int
dim (_ :+: Nat d :+: _ :+: _ :+: _ :+: _) = d

isUargsOn :: Domains (S.ArgumentsOf NaturalMI) -> Bool
isUargsOn (_ :+: _ :+: _ :+: _ :+: _ :+: ua) = ua

usableArgsWhereApplicable :: MatrixDP -> F.Signature -> Prob.StartTerms -> Bool -> Prob.Strategy -> Trs.Trs -> Trs.Trs -> UsablePositions
usableArgsWhereApplicable MWithDP sig _                     _  _     _ _ = fullWithSignature compSig `union` emptyWithSignature nonCompSig
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
                                                   Nothing -> Incompatible
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
matrixConstraints mrel mdp ua st strict weak sig mp = strictChoice mrel absmi strict && weakTrsConstraints absmi weak && otherConstraints mk absmi
  where absmi      = abstractInterpretation mk d sig :: MatrixInter (DioPoly DioVar Int)
        d          = dim mp
        mk         = kind mp st
        uaOn       = isUargsOn mp
        otherConstraints UnrestrictedMatrix mi = dpChoice mdp st uaOn mi
        otherConstraints TriangularMatrix mi = dpChoice mdp st uaOn mi && triConstraints mi
        otherConstraints (ConstructorBased cs) mi = dpChoice mdp st uaOn mi && triConstraints mi'
                                                    where mi' = mi{interpretations = filterCs $ interpretations mi}
                                                          filterCs = Map.filterWithKey (\f _ -> f `Set.member` cs)
        strictChoice MDirect    = strictTrsConstraints
        strictChoice MRelative  = relativeStricterTrsConstraints
--         strictChoice MWeightGap = strictOneConstraints
        dpChoice MWithDP _                     _     = safeRedpairConstraints sig
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

safeRedpairConstraints :: AbstrOrdSemiring a b => F.Signature -> MatrixInter a -> b
safeRedpairConstraints sig = bigAnd . Map.map (bigAnd . Map.map ((.>=. SR.one) . entry 1 1) . coefficients) . compInterpretations
                             where compInterpretations = Map.filterWithKey isCompound . interpretations
                                   isCompound f _      = F.isCompound sig f

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
