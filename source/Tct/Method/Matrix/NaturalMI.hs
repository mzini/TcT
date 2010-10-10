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
import qualified Termlib.Trs as Trs
import qualified Termlib.Variable as V

import Tct.Certificate (poly, expo, certified, unknown)
import Tct.Encoding.AbstractInterpretation
import Tct.Encoding.Matrix hiding (maxMatrix)
import Tct.Encoding.Natring ()
import Tct.Method.Matrix.MatrixInterpretation
import Tct.Processor.Args
import qualified Tct.Processor.Args as A
import Tct.Processor.Args.Instances
import Tct.Processor.Args.Instances ()
import Tct.Processor.Orderings
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
                               , param    :: MatrixKind }

data NaturalMI = NaturalMI deriving (Typeable, Show)

instance PrettyPrintable MatrixOrder where
    pprint order = (text "The input is compatible using the following" <+> ppknd (param order) <+> text "matrix interpretation:")
                   $+$ pprint (ordInter order)
        where ppknd UnrestrictedMatrix   = text "unrestricted"
              ppknd TriangularMatrix     = text "triangular"
              ppknd (ConstructorBased _) = text "constructor-restricted"

instance Answerable MatrixOrder where
    answer (MatrixOrder _ UnrestrictedMatrix)    = CertAnswer $ certified (unknown, expo (Just 1))
    answer (MatrixOrder m TriangularMatrix)      = CertAnswer $ certified (unknown, poly (Just (diagonalNonZeroes $ maxMatrix m)))
    answer (MatrixOrder m (ConstructorBased cs)) = CertAnswer $ certified (unknown, poly (Just (diagonalNonZeroes $ maxMatrix m')))
        where m'       = m{interpretations = filterCs $ interpretations m}
              filterCs = Map.filterWithKey (\f _ -> f `Set.member` cs)

instance ComplexityProof MatrixOrder

instance S.Processor NaturalMI where
    name NaturalMI = "matrix"

    description NaturalMI = [ "This processor orients the problem using matrix-interpretation over natural numbers." ]

    type S.ArgumentsOf NaturalMI = (Arg (EnumOf NaturalMIKind)) :+: (Arg Nat) :+: (Arg Nat)  :+: (Arg (Maybe Nat))  :+: (Arg (Maybe Nat))
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
                                                        , "For more information on matrix interpretations for complexity analysis "
                                                        , "cf. http://cl-informatik.uibk.ac.at/research/publications/2008/complexity-analysis-of-term-rewriting-based-on-mat/ ." 
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

    instanceName inst = "matrix-interpretation of dimension " ++ show (dim inst)

    type S.ProofOf NaturalMI = OrientationProof MatrixOrder
    solve inst problem = case Prob.relation problem of
                           Standard sr    -> orientDirect st sr sig inst
                           Relative sr wr -> orientRelative st sr wr sig inst
                           DP sr wr       -> orientDp st sr wr sig inst
        where sig = Prob.signature problem
              st  = Prob.startTerms problem


matrixProcessor :: S.StdProcessor NaturalMI
matrixProcessor = S.StdProcessor NaturalMI

matrix :: NaturalMIKind -> Nat -> N.Size -> Maybe Nat -> P.InstanceOf (S.StdProcessor NaturalMI)
matrix matrixkind matrixdimension coefficientsize constraintbits = 
    NaturalMI `S.withArgs` (matrixkind :+: matrixdimension :+: Nat (N.bound coefficientsize) :+: Nothing :+: constraintbits)

-- argument accessors

kind :: S.TheProcessor NaturalMI -> Prob.StartTerms -> MatrixKind
kind = kind' . S.processorArgs 
    where kind' (Unrestricted :+: _ :+: _ :+: _ :+: _) _                      = UnrestrictedMatrix
          kind' (Constructor  :+: _ :+: _ :+: _ :+: _) (Prob.BasicTerms _ cs) = ConstructorBased cs
          kind' (Constructor  :+: _ :+: _ :+: _ :+: _) Prob.TermAlgebra       = error "Constructor based matrix interpretations inapplicable for derivational complexity"
          kind' (Default      :+: _ :+: _ :+: _ :+: _) (Prob.BasicTerms _ cs) = ConstructorBased cs
          kind' (Default      :+: _ :+: _ :+: _ :+: _) Prob.TermAlgebra       = TriangularMatrix
          kind' (Triangular   :+: _ :+: _ :+: _ :+: _) _                      = TriangularMatrix

bound :: S.TheProcessor NaturalMI -> N.Size
bound inst = case mbits of 
               Just (Nat b) -> N.Bits b
               Nothing      -> N.Bound bnd
    where (_ :+: _ :+: Nat bnd :+: mbits :+: _) = S.processorArgs inst

cbits :: S.TheProcessor NaturalMI -> Maybe N.Size
cbits inst = do Nat n <- b
                return $ N.Bits n
    where (_ :+: _ :+: _ :+: _ :+: b) = S.processorArgs inst

dim :: S.TheProcessor NaturalMI -> Int
dim inst = d where (_ :+: Nat d :+: _ :+: _ :+: _) = S.processorArgs inst


orientDirect :: P.SolverM m => Prob.StartTerms -> Trs.Trs -> F.Signature -> S.TheProcessor NaturalMI -> m (S.ProofOf NaturalMI)
orientDirect st trs = orientMatrix relativeConstraints st trs Trs.empty

orientRelative :: P.SolverM m => Prob.StartTerms -> Trs.Trs -> Trs.Trs -> F.Signature -> S.TheProcessor NaturalMI -> m (S.ProofOf NaturalMI)
orientRelative = orientMatrix relativeConstraints

orientDp :: P.SolverM m => Prob.StartTerms -> Trs.Trs -> Trs.Trs -> F.Signature -> S.TheProcessor NaturalMI -> m (S.ProofOf NaturalMI)
orientDp = orientMatrix dpConstraints

orientMatrix :: P.SolverM m => (Prob.StartTerms -> Trs.Trs -> Trs.Trs -> F.Signature -> S.TheProcessor NaturalMI -> DioFormula MiniSatLiteral DioVar Int) 
             -> Prob.StartTerms -> Trs.Trs -> Trs.Trs -> F.Signature -> S.TheProcessor NaturalMI -> m (S.ProofOf NaturalMI)
orientMatrix f st dps trs sig mp = do theMI <- P.minisatValue addAct mi
                                      return $ case theMI of
                                                 Nothing -> Incompatible
                                                 Just mv -> Order $ MatrixOrder (fmap (\x -> x n) mv) mk
                                    where addAct :: MiniSat ()
                                          addAct = toFormula (liftM N.bound cb) (N.bound n) (f st dps trs sig mp) >>= SatSolver.addFormula
                                          mi     = abstractInterpretation mk d (sig `F.restrictToSymbols` Trs.functionSymbols (dps `Trs.union` trs)) :: MatrixInter (N.Size -> Int)
                                          n      = bound mp
                                          cb     = cbits mp
                                          d      = dim mp
                                          mk     = kind mp st

data MatrixDP = MWithDP | MNoDP deriving Show
data MatrixRelativity = MDirect | MRelative | MWeightGap deriving Show


relativeConstraints :: Eq l => Prob.StartTerms -> Trs.Trs -> Trs.Trs -> F.Signature -> S.TheProcessor NaturalMI -> DioFormula l DioVar Int
relativeConstraints = matrixConstraints MDirect MNoDP

dpConstraints :: Eq l => Prob.StartTerms -> Trs.Trs -> Trs.Trs -> F.Signature -> S.TheProcessor NaturalMI -> DioFormula l DioVar Int
dpConstraints = matrixConstraints MDirect MWithDP

-- TODO: rename derivationGraph
weightGapConstraints :: Eq l => Prob.StartTerms -> Trs.Trs -> Trs.Trs -> F.Signature -> S.TheProcessor NaturalMI -> DioFormula l DioVar Int
weightGapConstraints = matrixConstraints MWeightGap MNoDP

matrixConstraints :: Eq l => MatrixRelativity -> MatrixDP -> Prob.StartTerms -> Trs.Trs -> Trs.Trs -> F.Signature -> S.TheProcessor NaturalMI -> DioFormula l DioVar Int
matrixConstraints mrel mdp st strict weak sig mp = strictChoice mrel absmi strict && weakTrsConstraints absmi weak && otherConstraints mk absmi
  where absmi      = abstractInterpretation mk d (sig `F.restrictToSymbols` Trs.functionSymbols (strict `Trs.union` weak)) :: MatrixInter (DioPoly DioVar Int)
        d          = dim mp
        mk         = kind mp st
        otherConstraints UnrestrictedMatrix mi = dpChoice mdp mi
        otherConstraints TriangularMatrix mi = dpChoice mdp mi && triConstraints mi
        otherConstraints (ConstructorBased cs) mi = dpChoice mdp mi && triConstraints mi'
                                                    where mi' = mi{interpretations = filterCs $ interpretations mi}
                                                          filterCs = Map.filterWithKey (\f _ -> f `Set.member` cs)
        strictChoice MDirect    = strictTrsConstraints
        strictChoice MRelative  = relativeStrictTrsConstraints
        strictChoice MWeightGap = strictOneConstraints
        dpChoice MWithDP = safeRedpairConstraints sig
        dpChoice MNoDP   = monotoneConstraints

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
