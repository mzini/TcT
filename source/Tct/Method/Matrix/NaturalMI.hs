{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE TypeOperators #-}

{- | 
Module      :  Tct.Method.Poly.NaturalPI
Copyright   :  (c) Martin Avanzini <martin.avanzini@uibk.ac.at>, 
               Georg Moser <georg.moser@uibk.ac.at>, 
               Andreas Schnabl <andreas.schnabl@uibk.ac.at>
License     :  LGPL (see COPYING)

Maintainer  :  Andreas Schnabl <andreas.schnabl@uibk.ac.at>
Stability   :  unstable
Portability :  unportable      

This module defines the processor for matrix.
-}
module Tct.Method.Matrix.NaturalMI where

import Control.Monad (liftM)
import Control.Monad.Error (liftIO)
import qualified Control.Exception as E
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

import Termlib.Utils
import qualified Tct.Utils.Xml as Xml
import qualified Termlib.FunctionSymbol as F
import qualified Termlib.Problem as Prob
import qualified Termlib.Rule as R
import qualified Termlib.Trs as Trs
import qualified Termlib.Variable as V

import Tct.Certificate (poly, expo, certified, unknown)
import Tct.Encoding.AbstractInterpretation
import Tct.Encoding.Matrix hiding (maxMatrix)
import Tct.Encoding.Natring ()
import Tct.Encoding.UsablePositions hiding (empty)
import Tct.Method.Matrix.MatrixInterpretation as MI
import Tct.Processor.Args
import qualified Tct.Processor.Args as A
import Tct.Processor.Args.Instances
import Tct.Processor.Args.Instances ()
import Tct.Processor.Orderings
import Tct.Utils.PPrint (indent)
import qualified Tct.Processor as P
import Tct.Processor (Answer(..), ComplexityProof(..))
import qualified Tct.Processor.Standard as S

-- | This parameter defines the shape of the matrix interpretations, 
-- and how the induced complexity is computed.
data NaturalMIKind = Algebraic -- ^ Count number of ones in diagonal to compute induced complexity function.
                   | Automaton -- ^ Use automaton-techniques to compute induced complexity function.
                   | Triangular -- ^ Use triangular matrices only.
                   | Unrestricted -- ^ Put no further restrictions on the interpretation.
                     deriving (Typeable, Bounded, Enum, Eq)

instance Show NaturalMIKind where 
    show Algebraic    = "algebraic"
    show Triangular   = "triangular"    
    show Automaton    = "automaton"
    show Unrestricted = "nothing"

data MatrixOrder = MatrixOrder { ordInter :: MatrixInter Int
                               , param    :: MatrixKind
                               , miKind   :: NaturalMIKind
                               , uargs    :: UsablePositions } deriving Show

data NaturalMI = NaturalMI deriving (Typeable, Show)

instance PrettyPrintable (MatrixOrder, Trs.Trs, V.Variables) where
    pprint (order, trs, var) = pprintProof order P.ProofOutput $+$ pptrs
        where sig = signature $ ordInter order
              pptrs = text "Interpretations of rules:" $+$ vcat (map pprule $ Trs.rules trs)
              pprule r = (text "Rule" <+> pprint (r, sig, var) <+> char ':') $+$ ppterm (R.lhs r) $+$ ppterm (R.rhs r)
              ppterm t = pprint (t, sig, var) <+> char '=' <+> pprint ((interpretTerm (ordInter order) t), var)

instance ComplexityProof MatrixOrder where
    pprintProof order _ = (if uargs order == fullWithSignature (signature $ ordInter order)
                            then empty
                            else paragraph "The following argument positions are usable:")
                                 $+$ indent (pprint (uargs order, signature $ ordInter order))
                                 $+$ text ""
                            $+$ paragraph ("TcT has computed following " ++ ppknd (param order))
                            $+$ text ""
                            $+$ indent(pprint (ordInter order))
        where ppknd UnrestrictedMatrix            = "unrestricted matrix interpretation."
              ppknd (TriangularMatrix Nothing)    = "triangular matrix interpretation."
              ppknd (TriangularMatrix (Just n))   = "triangular matrix interpretation. Note that " 
                                                    ++ "the diagonal of the component-wise maxima of interpretation-entries contains no more than "              
                                                    ++ show n ++ " non-zero entries."
              ppknd (ConstructorBased _ Nothing)  = "constructor-restricted matrix interpretation."
              ppknd (ConstructorBased _ (Just n)) = "constructor-restricted matrix interpretation. Note that " 
                                                    ++ "the diagonal of the component-wise maxima of interpretation-entries contains no more than "              
                                                    ++ show n ++ " non-zero entries."
              ppknd (EdaMatrix Nothing)           = "matrix interpretation satisfying not(EDA)."
              ppknd (EdaMatrix (Just n))          = "matrix interpretation satisfying not(EDA) and not(IDA(" ++ show n ++ "))."
              ppknd (ConstructorEda _ Nothing)    = "constructor-based matrix interpretation satisfying not(EDA)."
              ppknd (ConstructorEda _ (Just n))   = "constructor-based matrix interpretation satisfying not(EDA) and not(IDA(" ++ show n ++ "))."

    answer order = CertAnswer $ certified (unknown, ub)
       
      where m = ordInter order
            countDiagonal | miKind order == Triangular = const $ dimension m
                          | otherwise = diagonalNonZeroes
            ub = case param order of 
                   UnrestrictedMatrix {} -> expo (Just 1)
                   TriangularMatrix {} -> poly $ Just $ countDiagonal $ maxNonIdMatrix m
                      where 
                   ConstructorBased cs _ -> poly $ Just $ countDiagonal $ maxNonIdMatrix m'
                      where m' = m{interpretations = filterCs $ interpretations m}
                            filterCs = Map.filterWithKey (\f _ -> f `Set.member` cs)
                   EdaMatrix Nothing -> poly $ Just $ dimension m
                   EdaMatrix (Just n) -> poly $ Just n
                   ConstructorEda _ Nothing -> poly $ Just $ dimension m
                   ConstructorEda _ (Just n) -> poly $ Just $ n                   
    toXml (MatrixOrder ord knd _ uarg) = 
      Xml.elt "interpretation" [] (MI.toXml ord knd uarg)


instance S.Processor NaturalMI where
    name NaturalMI = "matrix"

    description NaturalMI = [ "This processor orients the problem using matrix interpretation over natural numbers." ]

    type ArgumentsOf NaturalMI = (Arg (EnumOf NaturalMIKind)) :+: (Arg (Maybe Nat)) :+: (Arg Nat) :+: (Arg Nat)  :+: (Arg (Maybe Nat))  :+: (Arg (Maybe Nat)) :+: (Arg Bool)
    arguments NaturalMI = opt { A.name        = "cert"
                              , A.description = unwords [ "This argument specifies restrictions on the matrix interpretation which induce polynomial growth of"
                                                        , "the interpretation of the considered starting terms relative to their size."
                                                        , "Here 'algebraic' refers to simple algebraic restrictions on matrices (in the current implementation,"
                                                        , "they are simply restricted to triangular shape, i.e. matrices where coefficients in the lower-left"
                                                        , "half below the diagonal are zero. Such matrix interpretations induce polynomial derivational-complexity." 
                                                        , "If 'automaton' is given as argument, then criteria from the theory of weighted automata are used instead"
                                                        , "(in the current implementation, the negations of the criteria EDA, and possibly IDA(n), in the case that"
                                                        , "the flag 'degree' is set, are used)."
                                                        , "If 'nothing' is given, then matrix interpretations of all function symbols are unrestricted."
                                                        , "Note that matrix interpretations produced with this option do not induce polynomial complexities in general."
                                                        , "The default value is 'automaton'."
                                                        ]
                              , A.defaultValue = Automaton}
                          :+:
                          opt { A.name        = "degree"
                              , A.description = unwords [ "This argument ensures that the complexity induced by the searched matrix interpretation is bounded by a"
                                                        , "polynomial of the given degree. Its internal effect is dictated by the value the argument 'cert' is set to."
                                                        , "If it is set to 'algebraic', this restricts the number of non-zero entries in the diagonals of the matrices."
                                                        , "If it is set to 'automaton', this set the paramter 'n' in the criterion 'not IDA(n)'."
                                                        , "Finally, if it is set to 'unrestricted', the effect of setting the 'degree' argument is unspecified."
                                                        ]
                              , A.defaultValue = Nothing}
                          :+:
                          opt { A.name        = "dim"
                              , A.description = unwords [ "This argument specifies the dimension of the vectors and square-matrices appearing"
                                                        , " in the matrix interpretation."]
                              , A.defaultValue = Nat 2 }
                          :+:
                          opt { A.name        = "bound"
                              , A.description = unwords [ "This argument specifies an upper-bound on coefficients appearing in the interpretation."
                                                        , "Such an upper-bound is necessary as we employ bit-blasting to SAT internally"
                                                        , "when searching for compatible matrix interpretations."]
                              , A.defaultValue = Nat 3 }
                          :+:
                          opt { A.name        = "bits"
                              , A.description = unwords [ "This argument plays the same role as 'bound',"
                                                        , "but instead of an upper-bound the number of bits is specified."
                                                        , "This argument overrides the argument 'bound'."]
                              , A.defaultValue = Nothing }
                          :+:
                          opt { A.name = "cbits"
                              , A.description = unwords [ "This argument specifies the number of bits used for intermediate results, "
                                                        , "as for instance coefficients of matrices obtained by interpreting"
                                                        , "left- and right-hand sides."]
                              , A.defaultValue = Nothing }
                          :+:
                          opt { A.name = "uargs"
                              , A.description = unwords [ "This argument specifies whether usable arguments are computed (if applicable)"
                                                        , "in order to relax the monotonicity constraints on the interpretation."]
                              , A.defaultValue = True }

    instanceName inst = "matrix interpretation of dimension " ++ show (dim $ S.processorArgs inst)

    type ProofOf NaturalMI = OrientationProof MatrixOrder

    solve inst problem 
       | Trs.isEmpty (Prob.strictTrs problem) = orientDp strat st sr wr sig' (S.processorArgs inst)
       | otherwise                            = orientRelative strat st sr wr sig' (S.processorArgs inst)
      where sig   = Prob.signature problem
            sig'  = sig `F.restrictToSymbols` Trs.functionSymbols (Prob.allComponents problem)
            st    = Prob.startTerms problem
            strat = Prob.strategy problem
            sr    = Prob.strictComponents problem
            wr    = Prob.weakComponents problem

    solvePartial inst oblrules problem 
          | Trs.isEmpty (Prob.strictTrs problem) = mkProof `liftM` orientPartialDp oblrules strat st sr wr sig' (S.processorArgs inst)
          | otherwise                            = mkProof `liftM` orientPartialRelative oblrules strat st sr wr sig' (S.processorArgs inst)
      where sig   = Prob.signature problem
            sig'  = sig `F.restrictToSymbols` Trs.functionSymbols (Prob.allComponents problem)
            st    = Prob.startTerms problem
            strat = Prob.strategy problem
            mkProof res@(Order ord) = 
               P.PartialProof { P.ppInputProblem = problem
                              , P.ppResult       = res 
                              , P.ppRemovableDPs = Trs.toRules $ strictRules mi $ Prob.dpComponents problem
                              , P.ppRemovableTrs = Trs.toRules $ strictRules mi $ Prob.trsComponents problem }
                  where mi = ordInter ord
            mkProof res = 
               P.PartialProof { P.ppInputProblem = problem
                              , P.ppResult       = res
                              , P.ppRemovableDPs = []
                              , P.ppRemovableTrs = [] }
            sr    = Prob.strictComponents problem
            wr    = Prob.weakComponents problem

matrixProcessor :: S.StdProcessor NaturalMI
matrixProcessor = S.StdProcessor NaturalMI

-- argument accessors

kind :: Domains (S.ArgumentsOf NaturalMI) -> Prob.StartTerms -> MatrixKind
kind (Unrestricted :+: _ :+: _ :+: _ :+: _ :+: _ :+: _) _                      = UnrestrictedMatrix
kind (Algebraic    :+: d :+: _ :+: _ :+: _ :+: _ :+: _) (Prob.BasicTerms _ cs) = ConstructorBased cs (fmap (\ (Nat n) -> n) d)
kind (Algebraic    :+: d :+: _ :+: _ :+: _ :+: _ :+: _) Prob.TermAlgebra {}    = TriangularMatrix (fmap (\ (Nat n) -> n) d)
kind (Triangular   :+: d :+: _ :+: _ :+: _ :+: _ :+: _) (Prob.BasicTerms _ cs) = ConstructorBased cs (fmap (\ (Nat n) -> n) d)
kind (Triangular   :+: d :+: _ :+: _ :+: _ :+: _ :+: _) Prob.TermAlgebra {}    = TriangularMatrix (fmap (\ (Nat n) -> n) d)
kind (Automaton    :+: d :+: _ :+: _ :+: _ :+: _ :+: _) (Prob.BasicTerms _ cs) = ConstructorEda cs (fmap (\ (Nat n) -> max 1 n) d)
kind (Automaton    :+: d :+: _ :+: _ :+: _ :+: _ :+: _) Prob.TermAlgebra {}    = EdaMatrix (fmap (\ (Nat n) -> max 1 n) d)

mikind :: Domains (S.ArgumentsOf NaturalMI) -> NaturalMIKind
mikind (k :+: _ :+: _ :+: _ :+: _ :+: _ :+: _) = k

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

usableArgsWhereApplicable :: MatrixDP -> F.Signature -> Prob.StartTerms -> Bool -> Prob.Strategy -> Trs.Trs -> UsablePositions
usableArgsWhereApplicable MWithDP sig _                     ua strat r = (if ua then restrictToSignature compSig (usableArgs strat r) else fullWithSignature compSig) `union` emptyWithSignature nonCompSig
  where compSig    = F.restrictToSymbols sig $ Set.filter (F.isCompound sig) $ F.symbols sig
        nonCompSig = F.restrictToSymbols sig $ Set.filter (not . F.isCompound sig) $ F.symbols sig
usableArgsWhereApplicable MNoDP   sig Prob.TermAlgebra {}     _  _     _ = fullWithSignature sig
usableArgsWhereApplicable MNoDP   sig Prob.BasicTerms {} ua strat r = if ua then usableArgs strat r else fullWithSignature sig

-- uastrat :: Domains (S.ArgumentsOf NaturalMI) -> UArgStrategy
-- uastrat (_ :+: _ :+: _ :+: _ :+: _ :+: uas) = uas


catchException :: P.SolverM m => m (S.ProofOf NaturalMI) -> m (S.ProofOf NaturalMI)
catchException m = 
  do io <- P.mkIO m 
     liftIO $ E.catchJust notKill io (return . ExceptionRaised)
  where notKill E.ThreadKilled = Nothing
        notKill e = Just e


orientRelative :: P.SolverM m => Prob.Strategy -> Prob.StartTerms -> Trs.Trs -> Trs.Trs -> F.Signature -> Domains (S.ArgumentsOf NaturalMI) -> m (S.ProofOf NaturalMI)
orientRelative strat st strict weak sig mp = orientMatrix relativeConstraints ua st strict weak sig mp
  where ua = usableArgsWhereApplicable MNoDP sig st (isUargsOn mp) strat (strict `Trs.union` weak)

orientDp :: P.SolverM m => Prob.Strategy -> Prob.StartTerms -> Trs.Trs -> Trs.Trs -> F.Signature -> Domains (S.ArgumentsOf NaturalMI) -> m (S.ProofOf NaturalMI)
orientDp strat st strict weak sig mp = orientMatrix dpConstraints ua st strict weak sig mp
  where ua = usableArgsWhereApplicable MWithDP sig st (isUargsOn mp) strat (strict `Trs.union` weak)

orientPartialDp :: P.SolverM m => [R.Rule] -> Prob.Strategy -> Prob.StartTerms -> Trs.Trs -> Trs.Trs -> F.Signature -> Domains (S.ArgumentsOf NaturalMI) -> m (S.ProofOf NaturalMI)
orientPartialDp oblrules strat st strict weak sig mp = orientMatrix (partialDpConstraints oblrules) ua st strict weak sig mp
  where ua = usableArgsWhereApplicable MWithDP sig st (isUargsOn mp) strat (strict `Trs.union` weak)

orientPartialRelative :: P.SolverM m => [R.Rule] -> Prob.Strategy -> Prob.StartTerms -> Trs.Trs -> Trs.Trs -> F.Signature -> Domains (S.ArgumentsOf NaturalMI) -> m (S.ProofOf NaturalMI)
orientPartialRelative oblrules strat st strict weak sig mp = orientMatrix (partialConstraints oblrules) ua st strict weak sig mp
  where ua = usableArgsWhereApplicable MNoDP sig st (isUargsOn mp) strat (strict `Trs.union` weak)


orientMatrix :: P.SolverM m => (UsablePositions -> Prob.StartTerms -> Trs.Trs -> Trs.Trs -> F.Signature -> Domains (S.ArgumentsOf NaturalMI) -> DioFormula MiniSatLiteral DioVar Int)
             -> UsablePositions -> Prob.StartTerms -> Trs.Trs -> Trs.Trs -> F.Signature -> Domains (S.ArgumentsOf NaturalMI) -> m (S.ProofOf NaturalMI)
orientMatrix f ua st dps trs sig mp = 
  catchException $ 
    do theMI <- P.minisatValue addAct mi
       return $ case theMI of
                  Nothing -> Incompatible -- useful for debug: Order $ MatrixOrder (MI 1 sig Map.empty) mk ua
                  Just mv -> Order $ MatrixOrder (fmap (\x -> x n) mv) mk (mikind mp) ua
    where addAct :: MiniSat ()
          addAct  = toFormula (liftM N.bound cb) (N.bound n) (f ua st dps trs sig mp) >>= SatSolver.addFormula
          mi      = abstractInterpretation mk d sig :: MatrixInter (N.Size -> Int)
          n       = bound mp
          cb      = cbits mp
          d       = dim mp
          mk      = kind mp st

data MatrixDP = MWithDP | MNoDP deriving Show
data MatrixRelativity = MDirect | MRelative [R.Rule] deriving Show

partialConstraints :: Eq l => [R.Rule] -> UsablePositions -> Prob.StartTerms -> Trs.Trs -> Trs.Trs -> F.Signature -> Domains (S.ArgumentsOf NaturalMI) -> DioFormula l DioVar Int
partialConstraints oblrules = matrixConstraints (MRelative oblrules) MNoDP

relativeConstraints :: Eq l => UsablePositions -> Prob.StartTerms -> Trs.Trs -> Trs.Trs -> F.Signature -> Domains (S.ArgumentsOf NaturalMI) -> DioFormula l DioVar Int
relativeConstraints = matrixConstraints MDirect MNoDP

dpConstraints :: Eq l => UsablePositions -> Prob.StartTerms -> Trs.Trs -> Trs.Trs -> F.Signature -> Domains (S.ArgumentsOf NaturalMI) -> DioFormula l DioVar Int
dpConstraints = matrixConstraints MDirect MWithDP

partialDpConstraints :: Eq l => [R.Rule] -> UsablePositions -> Prob.StartTerms -> Trs.Trs -> Trs.Trs -> F.Signature -> Domains (S.ArgumentsOf NaturalMI) -> DioFormula l DioVar Int
partialDpConstraints oblrules = matrixConstraints (MRelative oblrules) MWithDP


-- TODO: rename derivationGraph
-- weightGapConstraints :: Eq l => Prob.StartTerms -> Trs.Trs -> Trs.Trs -> F.Signature -> S.TheProcessor NaturalMI -> DioFormula l DioVar Int
-- weightGapConstraints = matrixConstraints MWeightGap MNoDP

data Strict = Strict R.Rule deriving (Eq, Ord, Show, Typeable)
instance PropAtom Strict


matrixConstraints :: Eq l => MatrixRelativity -> MatrixDP -> UsablePositions -> Prob.StartTerms -> Trs.Trs -> Trs.Trs -> F.Signature
                  -> Domains (S.ArgumentsOf NaturalMI) -> DioFormula l DioVar Int
matrixConstraints mrel mdp ua st strict weak sig mp = 
  orientationConstraints mrel 
  && dpChoice mdp st uaOn absmi 
  && otherConstraints mk absmi
  where absmi      = abstractInterpretation mk d sig :: MatrixInter (DioPoly DioVar Int)
        d          = dim mp
        mk         = kind mp st
        uaOn       = isUargsOn mp
        otherConstraints UnrestrictedMatrix _                = top
        otherConstraints (TriangularMatrix Nothing) _        = top -- triConstraints mi -- AS: triConstraints already enforced by presence of RestrictVars
        otherConstraints (TriangularMatrix (Just deg)) mi    = diagOnesConstraints deg mi -- triConstraints mi && -- AS: triConstraints already enforced by presence of RestrictVars
        otherConstraints (ConstructorBased _  Nothing) _     = top -- triConstraints mi' -- AS: triConstraints already enforced by presence of RestrictVars
                                                                   -- where mi' = mi{interpretations = filterCs $ interpretations mi}
                                                                   --       filterCs = Map.filterWithKey (\f _ -> f `Set.member` cs)
        otherConstraints (ConstructorBased cs (Just deg)) mi = diagOnesConstraints deg mi' -- triConstraints mi' && -- AS: triConstraints already enforced by presence of RestrictVars
                                                               where mi' = mi{interpretations = filterCs $ interpretations mi}
                                                                     filterCs = Map.filterWithKey (\f _ -> f `Set.member` cs)
        otherConstraints (EdaMatrix Nothing) mi              = edaConstraints mi
        otherConstraints (EdaMatrix (Just deg)) mi           = idaConstraints deg mi
        otherConstraints (ConstructorEda cs Nothing) mi      = rcConstraints (mi' ds) && edaConstraints (mi' cs)
                                                               where ds = F.symbols sig Set.\\ cs
                                                                     mi' fs = mi{interpretations = filterFs fs $ interpretations mi}
                                                                     filterFs fs = Map.filterWithKey (\f _ -> f `Set.member` fs)
        otherConstraints (ConstructorEda cs (Just deg)) mi   = rcConstraints (mi' ds) && idaConstraints deg (mi' cs)
                                                               where ds = F.symbols sig Set.\\ cs
                                                                     mi' fs = mi{interpretations = filterFs fs $ interpretations mi}
                                                                     filterFs fs = Map.filterWithKey (\f _ -> f `Set.member` fs)
        orientationConstraints MDirect = strictTrsConstraints absmi strict && weakTrsConstraints absmi weak 

        orientationConstraints (MRelative oblrules) = 
           bigAnd [interpretTerm absmi (R.lhs r) .>=. (modify r $ interpretTerm absmi (R.rhs r)) | r <- Trs.rules $ strict `Trs.union` weak]
           && bigAnd [strictVar r .>. SR.zero | r <- oblrules]
           where modify r inter = inter { constant = case constant inter of  
                                             Vector (v:vs) -> Vector (v `SR.plus` strictVar r : vs)}
                 strictVar = restrictvar . Strict

        dpChoice MWithDP _                   u     = safeRedpairConstraints sig ua u
        dpChoice MNoDP   Prob.TermAlgebra {} _     = monotoneConstraints
        dpChoice MNoDP   Prob.BasicTerms {}  True  = uargMonotoneConstraints ua
        dpChoice MNoDP   Prob.BasicTerms {}  False = monotoneConstraints

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

-- Fixing the number of ones in diagonals

data DiagOnesVar = DiagOnesVar Int
                 deriving (Eq, Ord, Show, Typeable)

instance PropAtom DiagOnesVar

diagOnesConstraints :: Eq l => Int -> MatrixInter (DioPoly DioVar Int) -> DioFormula l DioVar Int
-- diagOnesConstraints :: (RingConst a, AbstrOrdSemiring a b) => Int -> MatrixInter a -> b
diagOnesConstraints deg mi = diagOnesVars && maxDegree
  where d = dimension mi
        toD = [1..d]
        diagOnesVars = bigAnd [ ((restrictvar $ DiagOnesVar x) .==. (SR.one :: DioPoly DioVar Int)) <-> f x  | x <- toD ]
        f x = bigOr $ map (bigOr . map (\ m -> entry x x m .>=. SR.one) . Map.elems . coefficients) $ Map.elems $ interpretations mi
        maxDegree = (constToPoly deg :: DioPoly DioVar Int) .>=. SR.bigPlus [ restrictvar $ DiagOnesVar x | x <- toD ]

-- Automaton Stuff
-- Notation follows the 5-author CAI paper

data XdaVar = Gtwo Int Int Int Int
            | R Int Int
            | Done Int Int Int
            | Dtwo Int Int Int
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
edaConstraints mi = rConstraints mi && dConstraints mi && gtwoConstraints mi -- && goneConstraints mi

idaConstraints :: Eq l => Int -> MatrixInter (DioPoly DioVar Int) -> DioFormula l DioVar Int
idaConstraints deg mi = rConstraints mi && tConstraints mi && iConstraints mi && jConstraints mi && hConstraints deg mi && gThreeConstraints mi -- && edaConstraints mi

rcConstraints :: Eq l => MatrixInter (DioPoly DioVar Int) -> DioFormula l DioVar Int
rcConstraints mi = bigAnd [ ggeq mi 1 x --> dioAtom (R 1 x) | x <- toD ]
  where d = dimension mi
        toD = [1..d]

-- goneConstraints :: Eq l => MatrixInter (DioPoly DioVar Int) -> DioFormula l DioVar Int
-- goneConstraints mi = bigAnd [ f i j | i <- toD, j <- toD ]
--   where d     = dimension mi
--         toD   = [1..d]
--         f i j = g i j && h i j
--         g i j = (dioAtom $ Ggeq i j) <-> bigOr (map (bigOr . map (\ m -> entry i j m .>=. SR.one) . Map.elems . coefficients) $ Map.elems $ interpretations mi)
--         h i j = (dioAtom $ Ggrt i j) <-> bigOr (map (bigOr . map (\ m -> entry i j m .>. SR.one) . Map.elems . coefficients) $ Map.elems $ interpretations mi)

gtwoConstraints :: Eq l => MatrixInter (DioPoly DioVar Int) -> DioFormula l DioVar Int
gtwoConstraints mi  = bigAnd [ f i j k l | i <- toD, j <- toD, k <- toD, l <- toD ]
  where d           = dimension mi
        toD         = [1..d]
        f i j k l   = (dioAtom $ Gtwo i j k l) <-> bigOr (map (bigOr . map (g i j k l) . Map.elems . coefficients) $ Map.elems $ interpretations mi)
        g i j k l m = (entry i k m .>=. SR.one) && (entry j l m .>=. SR.one)

ggeq :: Eq l => MatrixInter (DioPoly DioVar Int) -> Int -> Int -> DioFormula l DioVar Int
ggeq mi i j = bigOr (map (bigOr . map (\ m -> entry i j m .>=. SR.one) . Map.elems . coefficients) $ Map.elems $ interpretations mi)

ggrt :: Eq l => MatrixInter (DioPoly DioVar Int) -> Int -> Int -> DioFormula l DioVar Int
ggrt mi i j = bigOr (map (bigOr . map (\ m -> entry i j m .>. SR.one) . Map.elems . coefficients) $ Map.elems $ interpretations mi)

gtwo :: Eq l => MatrixInter (DioPoly DioVar Int) -> Int -> Int -> Int -> Int -> DioFormula l DioVar Int
gtwo mi i j k l = bigOr (map (bigOr . map g . Map.elems . coefficients) $ Map.elems $ interpretations mi)
  where g m = (entry i k m .>=. SR.one) && (entry j l m .>=. SR.one)

rConstraints :: Eq l => MatrixInter (DioPoly DioVar Int) -> DioFormula l DioVar Int
rConstraints mi = reflexivity && transitivity && compatibility && nocycle
  where d   = dimension mi
        toD = [1..d]
        reflexivity   = bigAnd $ map (\ x -> dioAtom (R x x)) toD
        transitivity  = bigAnd [ (dioAtom (R x y) && dioAtom (R y z)) --> dioAtom (R x z) | x <- toD, y <- toD, z <- toD ]
        compatibility = bigAnd [ ggeq mi x y --> dioAtom (R x y) | x <- toD, y <- toD ]
        nocycle       = bigAnd [ (dioAtom (R 1 y) && ggrt mi x y) --> not (dioAtom (R y x)) | x <- toD, y <- toD ]

dConstraints :: Eq l => MatrixInter (DioPoly DioVar Int) -> DioFormula l DioVar Int
dConstraints mi = foreapprox && forecompat && backapprox && backcompat && exactness
  where d           = dimension mi
        toD         = [1..d]
--        diagonal    = bigAnd [ if x == y then dioAtom (D x y) else not (dioAtom $ D x y) | x <- toD, y <- toD ]
        foreapprox  = bigAnd [ dioAtom (R 1 x) --> dioAtom (Done x x x) | x <- toD ]
        forecompat  = bigAnd [ (dioAtom (Done i x y) && dioAtom (Gtwo x y z u)) --> dioAtom (Done i z u) | i <- toD, x <- toD, y <- toD, z <- toD, u <- toD ]
        backapprox  = bigAnd [ dioAtom (R 1 x) --> dioAtom (Dtwo x x x) | x <- toD ]
        backcompat  = bigAnd [ (dioAtom (Dtwo i x y) && dioAtom (Gtwo z u x y)) --> dioAtom (Dtwo i z u) | i <- toD, x <- toD, y <- toD, z <- toD, u <- toD ]
        exactness   = bigAnd [ if x == y then top else not (dioAtom (Done i x y) && dioAtom (Dtwo i x y)) | i <- toD, x <- toD, y <- toD ]

gThreeConstraints :: Eq l => MatrixInter (DioPoly DioVar Int) -> DioFormula l DioVar Int
gThreeConstraints mi = bigAnd [ f i j k x y z | i <- toD, j <- toD, k <- toD, x <- toD, y <- toD, z <- toD ]
  where d         = dimension mi
        toD       = [1..d]
        f i j k x y z = (dioAtom $ Gthree i j k x y z) <-> bigOr (map (bigOr . map (g i j k x y z) . Map.elems . coefficients) $ Map.elems $ interpretations mi)
        g i j k x y z m = (entry i x m .>=. SR.one) && (entry j y m .>=. SR.one) && (entry k z m .>=. SR.one)

gthree :: Eq l => MatrixInter (DioPoly DioVar Int) -> Int -> Int -> Int -> Int -> Int -> Int -> DioFormula l DioVar Int
gthree mi i j k x y z = bigOr (map (bigOr . map g . Map.elems . coefficients) $ Map.elems $ interpretations mi)
  where g m = (entry i x m .>=. SR.one) && (entry j y m .>=. SR.one) && (entry k z m .>=. SR.one)

tConstraints :: Eq l => MatrixInter (DioPoly DioVar Int) -> DioFormula l DioVar Int
tConstraints mi = initial && gThreeStep
  where d = dimension mi
        toD = [1..d]
        initial = bigAnd [ if x == y then top else (dioAtom (R 1 x) && dioAtom (R 1 y)) --> dioAtom (T x x y) | x <- toD, y <- toD ]
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
        unaryNotation = bigAnd [ dioAtom (H x h) --> dioAtom (H x (h - 1)) | x <- toD, h <- [2..deg - 1] ]
        jDecrease = bigAnd [ f i j | i <- toD, j <- toD ]
        f i j = dioAtom (J i j) --> bigOr (map (\ h -> dioAtom (H i h) && not (dioAtom $ H j h)) [1..deg - 1])

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
  plus = N.mAddNO
  prod = N.mTimesNO
  zero = N.natToFormula 0
  one  = N.natToFormula 1
  geq  = N.mGeq
  grt  = N.mGrt
  equ  = N.mEqu
  constToFormula = N.natToFormula
  formAtom = N.natAtomM . N.Bound
  truncFormTo = N.mTruncTo
  padFormTo n f = N.padBots (max n l - l) f
    where l = length f

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
