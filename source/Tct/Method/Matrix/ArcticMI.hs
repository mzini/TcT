{- | 
Module      :  Tct.Method.Matrix.ArcticMI
Copyright   :  (c) Martin Avanzini <martin.avanzini@uibk.ac.at>, 
               Georg Moser <georg.moser@uibk.ac.at>, 
               Andreas Schnabl <andreas.schnabl@uibk.ac.at>
License     :  LGPL (see COPYING)

Maintainer  :  Andreas Schnabl <andreas.schnabl@uibk.ac.at>
Stability   :  unstable
Portability :  unportable      

This module defines the processor arctic.
-}

{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE TypeOperators #-}

module Tct.Method.Matrix.ArcticMI where

import Prelude hiding ((+), (&&), (||), not)
import Data.Typeable
import Control.Monad (liftM)
import Text.PrettyPrint.HughesPJ
import qualified Prelude as Prelude
import qualified Data.Map as Map
import qualified Data.Set as Set

import Qlogic.Arctic hiding (max)
import Qlogic.Diophantine
import Qlogic.Boolean
import Qlogic.MiniSat
import Qlogic.Semiring
import qualified Qlogic.ArcSat as AS
import qualified Qlogic.Semiring as SR
import qualified Qlogic.SatSolver as SatSolver

import Termlib.Utils
import qualified Termlib.FunctionSymbol as F
import qualified Termlib.Problem as Prob
import qualified Termlib.Rule as R
import qualified Termlib.Trs as Trs
import qualified Termlib.Variable as V

import Tct.Certificate (poly, certified, unknown)
import Tct.Encoding.AbstractInterpretation
import Tct.Encoding.Matrix
import Tct.Encoding.Natring ()
import Tct.Encoding.UsablePositions
import Tct.Method.Matrix.MatrixInterpretation
import Tct.Processor.Args
import Tct.Processor.Args.Instances
import Tct.Processor.Orderings
import qualified Tct.Processor.Args as A
import qualified Tct.Processor as P
import Tct.Processor (ComplexityProof(..),Answer(..))
import qualified Tct.Processor.Standard as S

data ArcticOrder = ArcticOrder { ordInter :: MatrixInter ArcInt
                               , uargs    :: UsablePositions} deriving Show

data ArcticMI = ArcticMI deriving (Typeable, Show)

instance ComplexityProof ArcticOrder where
    pprintProof order _ = 
        text "The following argument positions are usable:"
        $+$ pprint (uargs order, signature $ ordInter order)
        $+$ paragraph ("The input is compatible using the following arctic interpretation.")
        $+$ pprint (ordInter order)
    answer (ArcticOrder _ _) = CertAnswer $ certified (unknown, poly (Just 1))


instance S.Processor ArcticMI where
    name ArcticMI = "arctic"

    description ArcticMI = [ "This processor orients the problem using matrix interpretation over the arctic semiring." ]

    type ArgumentsOf ArcticMI = (Arg Nat) :+: (Arg Nat) :+: (Arg (Maybe Nat)) :+: (Arg (Maybe Nat)) :+: (Arg Bool)
    arguments ArcticMI =  opt { A.name        = "dim"
                              , A.description = unlines [ "This argument specifies the dimension of the vectors and square-matrices appearing"
                                                        , " in the matrix interpretation."]
                              , A.defaultValue = Nat 3 }
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

    instanceName inst = "arctic-interpretation of dimension " ++ show (dim inst)

    type ProofOf ArcticMI = OrientationProof ArcticOrder
    solve inst problem  | not isMonadic                        = return $ Inapplicable "Arctic Interpretations only applicable for monadic problems"
                        | Trs.isEmpty (Prob.strictTrs problem) = orientDp strat st sr wr sig inst
                        | otherwise                            = orientRelative strat st sr wr sig inst
        where sig   = Prob.signature problem
              st    = Prob.startTerms problem
              strat = Prob.strategy problem
              sr    = Prob.strictComponents problem
              wr    = Prob.weakComponents problem
              isMonadic | Trs.isEmpty (Prob.strictTrs problem) = allMonadic $ Set.filter (F.isCompound sig) $ Trs.functionSymbols wr
                        | otherwise                            = allMonadic $ Trs.functionSymbols $ Prob.allComponents problem
              allMonadic = all (\ f -> F.arity sig f Prelude.<= 1) . Set.toList

    solvePartial inst oblrules problem | not isMonadic = return $ P.PartialProof { P.ppInputProblem = problem
                                                                        , P.ppResult       = Inapplicable "Arctic Interpretations only applicable for monadic problems"
                                                                        , P.ppRemovableDPs = []
                                                                        , P.ppRemovableTrs = [] }
                                       | Trs.isEmpty (Prob.strictTrs problem) = mkProof sdps strs `liftM` orientPartialDp oblrules strat st sr wr sig' inst
                                       | otherwise = mkProof sdps strs `liftM` orientPartialRelative oblrules strat st sr wr sig' inst
      where sig   = Prob.signature problem
            sig'  = sig `F.restrictToSymbols` Trs.functionSymbols (Prob.allComponents problem)
            st    = Prob.startTerms problem
            strat = Prob.strategy problem
            sr    = Prob.strictComponents problem
            wr    = Prob.weakComponents problem
            sdps  = Prob.strictDPs problem
            strs  = Prob.strictTrs problem
            mkProof dps trs res@(Order (ArcticOrder mi _)) = P.PartialProof { P.ppInputProblem = problem
                                                                            , P.ppResult       = res 
                                                                            , P.ppRemovableDPs = Trs.toRules $ strictRules mi dps
                                                                            , P.ppRemovableTrs = Trs.toRules $ strictRules mi trs }
            mkProof _   _   res                            = P.PartialProof { P.ppInputProblem = problem
                                                                            , P.ppResult       = res
                                                                            , P.ppRemovableDPs = []
                                                                            , P.ppRemovableTrs = [] }
            isMonadic = allMonadic $ Trs.functionSymbols $ Prob.allComponents problem
            allMonadic = all (\ f -> F.arity sig f Prelude.<= 1) . Set.toList
    --   where sig   = Prob.signature problem
    --         sig'  = sig `F.restrictToSymbols` Trs.functionSymbols (Prob.strictTrs problem `Trs.union` Prob.weakTrs problem)
    --         st    = Prob.startTerms problem
    --         strat = Prob.strategy problem
    --         mkProof sr res@(Order (ArcticOrder mi _)) = P.PartialProof { P.ppInputProblem = problem
    --                                                                    , P.ppResult       = res 
    --                                                                    , P.ppRemovable    = Trs.toRules $ strictRules mi sr}
    --         mkProof _  res                            = P.PartialProof { P.ppInputProblem = problem
    --                                                                    , P.ppResult       = res
    --                                                                    , P.ppRemovable    = [] }

arcticProcessor :: S.StdProcessor ArcticMI
arcticProcessor = S.StdProcessor ArcticMI

arctic :: Nat -> AS.Size -> Maybe Nat -> Bool -> P.InstanceOf (S.StdProcessor ArcticMI)
arctic matrixdimension coefficientsize constraintbits ua =
    S.StdProcessor ArcticMI `S.withArgs` (matrixdimension :+: Nat (AS.intbound coefficientsize) :+: Nothing :+: constraintbits :+: ua)

-- argument accessors

bound :: S.TheProcessor ArcticMI -> AS.Size
bound inst = case mbits of
               Just (Nat b) -> AS.Bits b
               Nothing      -> AS.Bound $ Fin bnd
    where (_ :+: Nat bnd :+: mbits :+: _ :+: _) = S.processorArgs inst

cbits :: S.TheProcessor ArcticMI -> Maybe AS.Size
cbits inst = do Nat n <- b
                return $ AS.Bits n
    where (_ :+: _ :+: _ :+: b :+: _) = S.processorArgs inst

dim :: S.TheProcessor ArcticMI -> Int
dim inst = d where (Nat d :+: _ :+: _ :+: _ :+: _) = S.processorArgs inst

isUargsOn :: S.TheProcessor ArcticMI -> Bool
isUargsOn inst = ua where (_ :+: _ :+: _ :+: _ :+: ua) = S.processorArgs inst

usableArgsWhereApplicable :: MatrixDP -> F.Signature -> Prob.StartTerms -> Bool -> Prob.Strategy -> Trs.Trs -> UsablePositions
usableArgsWhereApplicable MWithDP sig _                     _  _     _ = fullWithSignature compSig `union` emptyWithSignature nonCompSig
  where compSig    = F.restrictToSymbols sig $ Set.filter (F.isCompound sig) $ F.symbols sig
        nonCompSig = F.restrictToSymbols sig $ Set.filter (not . F.isCompound sig) $ F.symbols sig
usableArgsWhereApplicable MNoDP   sig Prob.TermAlgebra      _  _     _ = fullWithSignature sig
usableArgsWhereApplicable MNoDP   sig (Prob.BasicTerms _ _) ua strat r = if ua then usableArgs strat r else fullWithSignature sig

instance PrettyPrintable ArcInt where
  pprint MinusInf = text "-inf"
  pprint (Fin n)  = int n

data MatrixDP = MWithDP | MNoDP deriving Show

data MatrixRelativity = MDirect | MRelative [R.Rule] deriving Show

orientDirect :: P.SolverM m => Prob.Strategy -> Prob.StartTerms -> Trs.Trs -> F.Signature -> S.TheProcessor ArcticMI -> m (S.ProofOf ArcticMI)
orientDirect strat st trs sig mp = orientMatrix relativeConstraints ua st trs Trs.empty sig mp
  where ua = usableArgsWhereApplicable MNoDP sig st (isUargsOn mp) strat trs

orientRelative :: P.SolverM m => Prob.Strategy -> Prob.StartTerms -> Trs.Trs -> Trs.Trs -> F.Signature -> S.TheProcessor ArcticMI -> m (S.ProofOf ArcticMI)
orientRelative strat st strict weak sig mp = orientMatrix relativeConstraints ua st strict weak sig mp
  where ua = usableArgsWhereApplicable MNoDP sig st (isUargsOn mp) strat (strict `Trs.union` weak)

orientDp :: P.SolverM m => Prob.Strategy -> Prob.StartTerms -> Trs.Trs -> Trs.Trs -> F.Signature -> S.TheProcessor ArcticMI -> m (S.ProofOf ArcticMI)
orientDp strat st strict weak sig mp = orientMatrix dpConstraints ua st strict weak sig mp
  where ua = usableArgsWhereApplicable MWithDP sig st (isUargsOn mp) strat (strict `Trs.union` weak)

orientPartial :: P.SolverM m => [R.Rule] -> Prob.Strategy -> Prob.StartTerms -> Trs.Trs -> F.Signature -> S.TheProcessor ArcticMI -> m (S.ProofOf ArcticMI)
orientPartial oblrules strat st trs sig mp = orientMatrix (partialConstraints oblrules) ua st trs Trs.empty sig mp
  where ua = usableArgsWhereApplicable MNoDP sig st (isUargsOn mp) strat trs

orientPartialRelative :: P.SolverM m => [R.Rule] -> Prob.Strategy -> Prob.StartTerms -> Trs.Trs -> Trs.Trs -> F.Signature -> S.TheProcessor ArcticMI -> m (S.ProofOf ArcticMI)
orientPartialRelative oblrules strat st strict weak sig mp = orientMatrix (partialConstraints oblrules) ua st strict weak sig mp
  where ua = usableArgsWhereApplicable MNoDP sig st (isUargsOn mp) strat (strict `Trs.union` weak)

orientPartialDp :: P.SolverM m => [R.Rule] -> Prob.Strategy -> Prob.StartTerms -> Trs.Trs -> Trs.Trs -> F.Signature -> S.TheProcessor ArcticMI -> m (S.ProofOf ArcticMI)
orientPartialDp oblrules strat st strict weak sig mp = orientMatrix (partialConstraints oblrules) ua st strict weak sig mp
  where ua = usableArgsWhereApplicable MWithDP sig st (isUargsOn mp) strat (strict `Trs.union` weak)

orientMatrix :: P.SolverM m => (UsablePositions -> Prob.StartTerms -> Trs.Trs -> Trs.Trs -> F.Signature -> S.TheProcessor ArcticMI -> DioFormula MiniSatLiteral DioVar ArcInt)
             -> UsablePositions -> Prob.StartTerms -> Trs.Trs -> Trs.Trs -> F.Signature -> S.TheProcessor ArcticMI -> m (S.ProofOf ArcticMI)
orientMatrix f ua st dps trs sig mp = do theMI <- P.minisatValue addAct mi
                                         return $ case theMI of
                                                    Nothing -> Incompatible
                                                    Just mv -> Order $ ArcticOrder (fmap (\x -> x n) mv) ua
                                      where addAct :: MiniSat ()
                                            addAct = toFormula (liftM AS.bound cb) (AS.bound n) (f ua st dps trs sig mp) >>= SatSolver.addFormula
                                            mi     = abstractInterpretation UnrestrictedMatrix d (sig `F.restrictToSymbols` Trs.functionSymbols (dps `Trs.union` trs)) :: MatrixInter (AS.Size -> ArcInt)
                                            n      = bound mp
                                            cb     = cbits mp
                                            d      = dim mp

partialConstraints :: Eq l => [R.Rule] -> UsablePositions -> Prob.StartTerms -> Trs.Trs -> Trs.Trs -> F.Signature -> S.TheProcessor ArcticMI -> DioFormula l DioVar ArcInt
partialConstraints oblrules = matrixConstraints (MRelative oblrules) MNoDP

relativeConstraints :: Eq l => UsablePositions -> Prob.StartTerms -> Trs.Trs -> Trs.Trs -> F.Signature -> S.TheProcessor ArcticMI -> DioFormula l DioVar ArcInt
relativeConstraints = matrixConstraints MDirect MNoDP

dpConstraints :: Eq l => UsablePositions -> Prob.StartTerms -> Trs.Trs -> Trs.Trs -> F.Signature -> S.TheProcessor ArcticMI -> DioFormula l DioVar ArcInt
dpConstraints = matrixConstraints MDirect MWithDP

matrixConstraints :: Eq l => MatrixRelativity -> MatrixDP -> UsablePositions -> Prob.StartTerms -> Trs.Trs -> Trs.Trs -> F.Signature -> S.TheProcessor ArcticMI -> DioFormula l DioVar ArcInt
matrixConstraints mrel mdp ua st strict weak sig mp = strictChoice mrel absmi strict && weakTrsConstraints absmi weak && otherConstraints absmi
  where absmi   = abstractInterpretation UnrestrictedMatrix d (sig `F.restrictToSymbols` Trs.functionSymbols (strict `Trs.union` weak)) :: MatrixInter (DioPoly DioVar ArcInt)
        d          = dim mp
        uaOn       = isUargsOn mp
        otherConstraints mi = dpChoice mdp st uaOn mi
        strictChoice MDirect              = strictTrsConstraints
        strictChoice (MRelative oblrules) = relativeStricterTrsConstraints oblrules
        dpChoice MWithDP _                     _     = safeRedpairConstraints sig
        dpChoice MNoDP   Prob.TermAlgebra      _     = monotoneConstraints sig
        dpChoice MNoDP   (Prob.BasicTerms _ _) True  = uargMonotoneConstraints sig ua
        dpChoice MNoDP   (Prob.BasicTerms _ _) False = monotoneConstraints sig

uargMonotoneConstraints :: AbstrOrdSemiring a b => F.Signature -> UsablePositions -> MatrixInter a -> b
uargMonotoneConstraints sig uarg mi = unaryConstraints strictUnaryInts && nullaryConstraints nullaryInts && weakMonotoneConstraints weakUnaryInts
  where strictUnaryInts = mi{interpretations = Map.filterWithKey (\ f _ -> isUsable f 1 uarg) $ interpretations unaryInts}
        weakUnaryInts = mi{interpretations = Map.filterWithKey (\ f _ -> not $ isUsable f 1 uarg) $ interpretations unaryInts}
        unaryInts = mi{interpretations = Map.filterWithKey (\ f _ -> F.arity sig f == 1) $ interpretations mi}
        nullaryInts = mi{interpretations = Map.filterWithKey (\ f _ -> F.arity sig f == 0) $ interpretations mi}

monotoneConstraints :: AbstrOrdSemiring a b => F.Signature -> MatrixInter a -> b
monotoneConstraints sig mi = unaryConstraints unaryInts && nullaryConstraints nullaryInts
  where unaryInts = mi{interpretations = Map.filterWithKey (\ f _ -> F.arity sig f == 1) $ interpretations mi}
        nullaryInts = mi{interpretations = Map.filterWithKey (\ f _ -> F.arity sig f == 0) $ interpretations mi}

safeRedpairConstraints :: AbstrOrdSemiring a b => F.Signature -> MatrixInter a -> b
safeRedpairConstraints sig mi = unaryConstraints unaryCompMI && nullaryConstraints nullaryCompMI && weakMonotoneConstraints noncompMI
                                where splitInterpretations = Map.partitionWithKey isCompound $ interpretations mi
                                      unaryCompMI          = mi{interpretations = Map.filterWithKey (\ f _ -> F.arity sig f == 1) $ interpretations compMI}
                                      nullaryCompMI        = mi{interpretations = Map.filterWithKey (\ f _ -> F.arity sig f == 0) $ interpretations compMI}
                                      compMI               = mi{interpretations = fst splitInterpretations}
                                      noncompMI            = mi{interpretations = snd splitInterpretations}
                                      isCompound f _       = F.isCompound sig f

weakMonotoneConstraints :: AbstrOrdSemiring a b => MatrixInter a -> b
weakMonotoneConstraints = bigAnd . Map.map (\ f -> (vEntry 1 (constant f) .>=. SR.one) || (bigOr $ Map.map ((.>=. SR.one) . entry 1 1) $ coefficients f)) . interpretations

unaryConstraints :: AbstrOrdSemiring a b => MatrixInter a -> b
unaryConstraints mi = unaryMats && unaryVecs
  where unaryMats = bigAnd $ Map.map (bigAnd . Map.map ((.>=. SR.one) . entry 1 1) . coefficients) $ interpretations mi
        unaryVecs = bigAnd $ Map.map (bigAnd . liftVector (map (.==. SR.zero)) . constant) $ interpretations mi

nullaryConstraints :: AbstrOrdSemiring a b => MatrixInter a -> b
nullaryConstraints mi = bigAnd $ Map.map ((.>=. SR.one) . vEntry 1 . constant) $ interpretations mi

checkDirect :: MatrixInter ArcInt -> Trs.Trs -> F.Signature -> Bool
checkDirect mi trs sig = strictTrsConstraints mi trs && monotoneCheck
  where monotoneCheck = unaryCheck && nullaryCheck
        unaryCheck = unaryMats && unaryVecs
        unaryMats = bigAnd $ Map.map (bigAnd . Map.map ((.>=. SR.one) . entry 1 1) . coefficients) unaryInts
        unaryVecs = bigAnd $ Map.map (bigAnd . liftVector (map (.==. SR.zero)) . constant) $ unaryInts
        unaryInts = Map.filterWithKey (\ f _ -> F.arity sig f == 1) $ interpretations mi
        nullaryCheck = bigAnd $ Map.map ((.>=. SR.one) . vEntry 1 . constant) $ nullaryInts
        nullaryInts = Map.filterWithKey (\ f _ -> F.arity sig f == 0) $ interpretations mi

strictRules :: MatrixInter ArcInt -> Trs.Trs -> Trs.Trs
strictRules mi = Trs.filterRules $ strictRuleConstraints mi

class AIEntry a

instance AIEntry ArcInt

instance AIEntry (DioPoly DioVar ArcInt)

instance AIEntry (DioFormula l DioVar ArcInt)

instance AIEntry a => AIEntry (Vector a)

instance (AbstrEq a b, AIEntry a) => AbstrEq (Vector a) b where
  (Vector vs) .==. (Vector ws) = bigAnd $ zipWith (.==.) vs ws

instance (AbstrOrd a b, AIEntry a) => AbstrOrd (Vector a) b where
  (Vector vs) .<. (Vector ws) = bigAnd $ zipWith (.<.) vs ws
  (Vector vs) .<=. (Vector ws) = bigAnd $ zipWith (.<=.) vs ws

instance (AbstrEq a b, AIEntry a) => AbstrEq (Matrix a) b where
  (Matrix vs) .==. (Matrix ws) = (Vector vs) .==. (Vector ws)

instance (AbstrOrd a b, AIEntry a) => AbstrOrd (Matrix a) b where
  (Matrix vs) .<. (Matrix ws) = (Vector vs) .<. (Vector ws)
  (Matrix vs) .<=. (Matrix ws) = (Vector vs) .<=. (Vector ws)

instance (AbstrEq a b, AIEntry a) => AbstrEq (LInter a) b where
  (LI lcoeffs lconst) .==. (LI rcoeffs rconst) = bigAnd (Map.elems zipmaps) && lconst .==. rconst
                                                 where zipmaps = Map.intersectionWith (.==.) lcoeffs rcoeffs

instance (AbstrOrd a b, AIEntry a) => AbstrOrd (LInter a) b where
  (LI lcoeffs lconst) .<. (LI rcoeffs rconst) = bigAnd (Map.elems zipmaps) && lconst .<. rconst
                                                where zipmaps = Map.intersectionWith (.<.) lcoeffs rcoeffs
  (LI lcoeffs lconst) .<=. (LI rcoeffs rconst) = bigAnd (Map.elems zipmaps) && lconst .<=. rconst
                                                 where zipmaps = Map.intersectionWith (.<=.) lcoeffs rcoeffs

instance (Ord l, SatSolver.Solver s l) => MSemiring s l (AS.ArcFormula l) DioVar ArcInt where
  plus = AS.mAdd
  prod = AS.mTimes
  zero = AS.arcToFormula MinusInf
  one  = AS.arcToFormula $ Fin 0
  geq  = (AS.mGeq)
  grt  = (AS.mGrt)
  equ  = (AS.mEqu)
  constToFormula = AS.arcToFormula
  formAtom = AS.arcAtomM . AS.Bound
  truncFormTo = AS.mTruncTo
  padFormTo n f = AS.padBots (max n l - l) f
    where l = length $ snd f

instance SatSolver.Decoder (MatrixInter (AS.Size -> ArcInt)) (AS.ArcBZVec DioVar) where
  add (AS.InfBit (DioVar y)) mi  = case cast y of
                                      Nothing -> mi
                                      Just x -> mi{interpretations = Map.adjust newli fun (interpretations mi)}
                                        where newli li | pos == 0  = li{constant = adjustv newval i (constant li)}
                                              newli li | otherwise = li{coefficients = newli' li}
                                              newli' li    = Map.adjust newm (V.Canon pos) (coefficients li)
                                              newm         = adjustm newval i j
                                              newval _ _   = MinusInf
                                              fun = varfun x
                                              pos = argpos x
                                              i   = varrow x
                                              j   = varcol x
  add (AS.BZVec (DioVar y) k) mi = case cast y of
                                      Nothing -> mi
                                      Just x -> mi{interpretations = Map.adjust newli fun (interpretations mi)}
                                        where newli li | pos == 0  = li{constant = adjustv newval i (constant li)}
                                              newli li | otherwise = li{coefficients = newli' li}
                                              newli' li    = Map.adjust newm (V.Canon pos) (coefficients li)
                                              newm         = adjustm newval i j
                                              newval old n = newval' (old n) n
                                              newval' MinusInf _  = MinusInf
                                              newval' (Fin old) n = Fin $ (f k) old (2 ^ ((if r then 1 else AS.bits n) - k))
                                              f k' = if k' == 1 then (Prelude.+) else (Prelude.+)
                                              r    = restrict x
                                              fun  = varfun x
                                              pos  = argpos x
                                              i    = varrow x
                                              j    = varcol x
