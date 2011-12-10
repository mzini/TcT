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
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeSynonymInstances #-}

module Tct.Method.Poly.NaturalPI where

import Prelude hiding ((&&),not)

import Control.Monad (liftM)
import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.Typeable
import Text.PrettyPrint.HughesPJ

import Qlogic.Boolean
import Qlogic.Diophantine
import Qlogic.MiniSat
import qualified Qlogic.NatSat as N
import qualified Qlogic.SatSolver as SatSolver
import Qlogic.Semiring
import qualified Qlogic.Semiring as SR

import qualified Termlib.FunctionSymbol as F
import qualified Termlib.Problem as Prob
import qualified Termlib.Rule as R
import qualified Termlib.Trs as Trs
import Termlib.Utils
import qualified Termlib.Variable as V

import Tct.Certificate (poly, expo, certified, unknown)
import Tct.Encoding.AbstractInterpretation
import Tct.Encoding.Natring ()
import Tct.Encoding.Polynomial
import Tct.Encoding.UsablePositions hiding (empty)
import Tct.Method.Poly.PolynomialInterpretation
import Tct.Processor (Answer(..), ComplexityProof(..))
import Tct.Processor.Args
import qualified Tct.Processor.Args as A
import Tct.Processor.Args.Instances
import Tct.Processor.Orderings
import Tct.Processor.PPrint (indent)
import qualified Tct.Processor as P
import qualified Tct.Processor.Standard as S

data PolynomialOrder = PolynomialOrder { ordInter :: PolyInter Int
                                       , param    :: PIKind
                                       , uargs    :: UsablePositions } deriving Show

data NaturalPI = NaturalPI deriving (Typeable, Show)

instance ComplexityProof PolynomialOrder where
  pprintProof order _ = 
      (if uargs order == fullWithSignature (signature $ ordInter order)
       then empty
       else (text "The following argument positions are usable:")
       $+$ indent (pprint (uargs order, signature $ ordInter order)))
      $+$ (text "We have the following" <+> ppknd (param order) <+> text "polynomial interpretation:")
      $+$ pprint (ordInter order)
    where ppknd (UnrestrictedPoly   shp) = ppshp shp
          ppknd (ConstructorBased _ shp) = text "restricted" <+> ppshp shp
          ppshp (SimpleShape s) = text (show s)
          ppshp (CustomShape _) = text ""          

  answer order = CertAnswer $ certified (unknown, ub)
    where ub = case knd of 
                 ConstructorBased _ _ -> poly (Just degree)
                 UnrestrictedPoly _ | isStrong && degree <= 1 -> poly (Just 1)
                                    | degree <= 1            -> expo (Just 1)
                                    | otherwise             -> expo (Just 2)
                 
          degree = foldl max 0 [ foldl max 0 [ maxdegree m | m <- monos] 
                                    | (f,(Poly monos)) <- inters, consider f ]
            where maxdegree (Mono 0 _)      = 0
                  maxdegree (Mono _ powers) = foldl (+) 0 [e | Pow _ e <- powers]
                  consider f = 
                    case knd of 
                      ConstructorBased cs _ -> not $ f `Set.member` cs
                      _                     -> True
          
          isStrong = all (all (\ (Mono n _) -> n <= 1)) [ monos | (_,Poly monos) <- inters]
          
          knd      = param order
          inters   = Map.toList $ interpretations $ ordInter order

instance S.Processor NaturalPI where
  name NaturalPI = "poly"

  description NaturalPI = [ "This processor orients the problem using polynomial interpretation over natural numbers." ]

  type S.ArgumentsOf NaturalPI = (Arg (Assoc PolyShape)) :+: (Arg Nat) :+: (Arg (Maybe Nat)) :+: (Arg (Maybe Nat)) :+: (Arg Bool)
  arguments NaturalPI = opt { A.name         = "kind"
                            , A.description  = unlines [ "This argument specifies the shape of the polynomials used in the interpretation."
                                                       , "Allowed values are 'stronglylinear', 'linear', 'simple', 'simplemixed', and 'quadratic',"
                                                       , "referring to the respective shapes of the abstract polynomials used."
                                                       , "The deault value is 'stronglylinear'." ]
                            , A.defaultValue = SimpleShape StronglyLinear }
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
                        opt { A.name        = "cbits"
                            , A.description = unlines [ "This argument specifies the number of bits used for intermediate results, "
                                                      , "as for instance coefficients of matrices obtained by interpreting"
                                                      , "left- and right-hand sides."]
                            , A.defaultValue = Nothing }
                        :+:
                        opt { A.name        = "uargs"
                            , A.description = unlines [ "This argument specifies whether usable arguments are computed (if applicable)"
                                                      , "in order to relax the monotonicity constraints on the interpretation."]
                            , A.defaultValue = True }

  instanceName inst = show (shape $ S.processorArgs inst) ++ " polynomial interpretation"

  type S.ProofOf NaturalPI = OrientationProof PolynomialOrder

  solve inst problem | Trs.isEmpty (Prob.strictTrs problem) = orientDp strat st sr wr sig' (S.processorArgs inst)
                     | otherwise                            = orientRelative strat st sr wr sig' (S.processorArgs inst)
    where sig   = Prob.signature problem
          sig'  = sig `F.restrictToSymbols` Trs.functionSymbols (Prob.allComponents problem)
          st    = Prob.startTerms problem
          strat = Prob.strategy problem
          sr    = Prob.strictComponents problem
          wr    = Prob.weakComponents problem

  solvePartial inst oblrules problem | Trs.isEmpty (Prob.strictTrs problem) = mkProof sdps strs `liftM` orientPartialDp oblrules strat st sr wr sig' (S.processorArgs inst)
                                     | otherwise                            = mkProof sdps strs `liftM` orientPartialRelative oblrules strat st sr wr sig' (S.processorArgs inst)
      where sig   = Prob.signature problem
            sig'  = sig `F.restrictToSymbols` Trs.functionSymbols (Prob.allComponents problem)
            st    = Prob.startTerms problem
            strat = Prob.strategy problem
            mkProof dps trs res@(Order (PolynomialOrder mi _ _)) = P.PartialProof { P.ppInputProblem = problem
                                                                                  , P.ppResult       = res 
                                                                                  , P.ppRemovableDPs = Trs.toRules $ strictRules mi dps
                                                                                  , P.ppRemovableTrs = Trs.toRules $ strictRules mi trs }
            mkProof _   _   res                                  = P.PartialProof { P.ppInputProblem = problem
                                                                                  , P.ppResult       = res
                                                                                  , P.ppRemovableDPs = []
                                                                                  , P.ppRemovableTrs = [] }
            sr    = Prob.strictComponents problem
            wr    = Prob.weakComponents problem
            sdps  = Prob.strictDPs problem
            strs  = Prob.strictTrs problem

polyProcessor :: S.StdProcessor NaturalPI
polyProcessor = S.StdProcessor NaturalPI

-- argument accessors

kind :: Domains (S.ArgumentsOf NaturalPI) -> Prob.StartTerms -> PIKind
kind args st = kind' (shape args) st
  where kind' shp Prob.TermAlgebra       = UnrestrictedPoly shp
        kind' shp (Prob.BasicTerms _ cs) = ConstructorBased cs shp

shape :: Domains (S.ArgumentsOf NaturalPI) -> PolyShape
shape (shp :+: _ :+: _ :+: _ :+: _) = shp

bound :: Domains (S.ArgumentsOf NaturalPI) -> N.Size
bound (_ :+: Nat bnd :+: mbits :+: _ :+: _) = case mbits of
                                                Just (Nat b) -> N.Bits b
                                                Nothing      -> N.Bound bnd

cbits :: Domains (S.ArgumentsOf NaturalPI) -> Maybe N.Size
cbits (_ :+: _ :+: _ :+: b :+: _) = do Nat n <- b
                                       return $ N.Bits n

isUargsOn :: Domains (S.ArgumentsOf NaturalPI) -> Bool
isUargsOn (_ :+: _ :+: _ :+: _ :+: ua) = ua

usableArgsWhereApplicable :: PolyDP -> F.Signature -> Prob.StartTerms -> Bool -> Prob.Strategy -> Trs.Trs -> Trs.Trs -> UsablePositions
usableArgsWhereApplicable PWithDP sig _                     ua strat r s = (if ua then restrictToSignature compSig (usableArgs strat r s) else fullWithSignature compSig) `union` emptyWithSignature nonCompSig
  where compSig    = F.restrictToSymbols sig $ Set.filter (F.isCompound sig) $ F.symbols sig
        nonCompSig = F.restrictToSymbols sig $ Set.filter (not . F.isCompound sig) $ F.symbols sig
usableArgsWhereApplicable PNoDP   sig Prob.TermAlgebra      _  _     _ _ = fullWithSignature sig
usableArgsWhereApplicable PNoDP   sig (Prob.BasicTerms _ _) ua strat r s = if ua then usableArgs strat r s else fullWithSignature sig

orientRelative :: P.SolverM m => Prob.Strategy -> Prob.StartTerms -> Trs.Trs -> Trs.Trs -> F.Signature -> Domains (S.ArgumentsOf NaturalPI) -> m (S.ProofOf NaturalPI)
orientRelative strat st strict weak sig mp = orientPoly relativeConstraints ua st strict weak sig mp
  where ua = usableArgsWhereApplicable PNoDP sig st (isUargsOn mp) strat Trs.empty (strict `Trs.union` weak)

orientDp :: P.SolverM m => Prob.Strategy -> Prob.StartTerms -> Trs.Trs -> Trs.Trs -> F.Signature -> Domains (S.ArgumentsOf NaturalPI) -> m (S.ProofOf NaturalPI)
orientDp strat st strict weak sig mp = orientPoly dpConstraints ua st strict weak sig mp
  where ua = usableArgsWhereApplicable PWithDP sig st (isUargsOn mp) strat Trs.empty (strict `Trs.union` weak)

orientPartialRelative :: P.SolverM m => [R.Rule] -> Prob.Strategy -> Prob.StartTerms -> Trs.Trs -> Trs.Trs -> F.Signature -> Domains (S.ArgumentsOf NaturalPI) -> m (S.ProofOf NaturalPI)
orientPartialRelative oblrules strat st strict weak sig mp = orientPoly (partialConstraints oblrules) ua st strict weak sig mp
  where ua = usableArgsWhereApplicable PNoDP sig st (isUargsOn mp) strat Trs.empty (strict `Trs.union` weak)

orientPartialDp :: P.SolverM m => [R.Rule] -> Prob.Strategy -> Prob.StartTerms -> Trs.Trs -> Trs.Trs -> F.Signature -> Domains (S.ArgumentsOf NaturalPI) -> m (S.ProofOf NaturalPI)
orientPartialDp oblrules strat st strict weak sig mp = orientPoly (partialDpConstraints oblrules) ua st strict weak sig mp
  where ua = usableArgsWhereApplicable PWithDP sig st (isUargsOn mp) strat Trs.empty (strict `Trs.union` weak)

orientPoly :: P.SolverM m => (UsablePositions -> Prob.StartTerms -> Trs.Trs -> Trs.Trs -> F.Signature -> Domains (S.ArgumentsOf NaturalPI) -> DioFormula MiniSatLiteral DioVar Int)
             -> UsablePositions -> Prob.StartTerms -> Trs.Trs -> Trs.Trs -> F.Signature -> Domains (S.ArgumentsOf NaturalPI) -> m (S.ProofOf NaturalPI)
orientPoly f ua st strict weak sig inst = do thePI <- P.minisatValue addAct i
                                             return $ case thePI of
                                                        Nothing -> Incompatible
                                                        Just pv -> let pint = fmap (\x -> x n) pv in
                                                                   Order $ PolynomialOrder pint{interpretations = Map.map (unEmpty . shallowSimp) $ interpretations pint} pk ua
  where addAct :: MiniSat ()
        addAct = toFormula (liftM N.bound cb) (N.bound n) (f ua st strict weak sig inst) >>= SatSolver.addFormula
        i      = abstractInterpretation pk sig :: PolyInter (N.Size -> Int)
        n      = bound inst
        cb     = cbits inst
        pk     = kind inst st

data PolyDP = PWithDP | PNoDP deriving Show
data PolyRelativity = PDirect | PRelative [R.Rule] deriving Show

partialConstraints :: Eq l => [R.Rule] -> UsablePositions -> Prob.StartTerms -> Trs.Trs -> Trs.Trs -> F.Signature -> Domains (S.ArgumentsOf NaturalPI) -> DioFormula l DioVar Int
partialConstraints oblrules = polyConstraints (PRelative oblrules) PNoDP

relativeConstraints :: Eq l => UsablePositions -> Prob.StartTerms -> Trs.Trs -> Trs.Trs -> F.Signature -> Domains (S.ArgumentsOf NaturalPI) -> DioFormula l DioVar Int
relativeConstraints = polyConstraints PDirect PNoDP

dpConstraints :: Eq l => UsablePositions -> Prob.StartTerms -> Trs.Trs -> Trs.Trs -> F.Signature -> Domains (S.ArgumentsOf NaturalPI) -> DioFormula l DioVar Int
dpConstraints = polyConstraints PDirect PWithDP

partialDpConstraints :: Eq l => [R.Rule] -> UsablePositions -> Prob.StartTerms -> Trs.Trs -> Trs.Trs -> F.Signature -> Domains (S.ArgumentsOf NaturalPI) -> DioFormula l DioVar Int
partialDpConstraints oblrules = polyConstraints (PRelative oblrules) PWithDP

polyConstraints :: Eq l => PolyRelativity -> PolyDP -> UsablePositions -> Prob.StartTerms -> Trs.Trs -> Trs.Trs -> F.Signature -> Domains (S.ArgumentsOf NaturalPI) -> DioFormula l DioVar Int
polyConstraints prel pdp ua st strict weak sig proc = strictChoice prel absi strict && weakTrsConstraints absi weak && dpChoice pdp st uaOn absi
  where absi = abstractInterpretation pk sig :: PolyInter (DioPoly DioVar Int)
        pk   = kind proc st
        uaOn = isUargsOn proc
        strictChoice PDirect              = strictTrsConstraints
        strictChoice (PRelative oblrules) = relativeStricterTrsConstraints oblrules
        dpChoice PWithDP _                     u     = safeRedpairConstraints ua u
        dpChoice PNoDP   Prob.TermAlgebra      _     = monotoneConstraints
        dpChoice PNoDP   (Prob.BasicTerms _ _) True  = uargMonotoneConstraints ua
        dpChoice PNoDP   (Prob.BasicTerms _ _) False = monotoneConstraints

-- handlefun in the next two functions could be replaced by something else,
-- e.g. a criterion by Friedl
uargMonotoneConstraints :: AbstrOrdSemiring a b => UsablePositions -> PolyInter a -> b
uargMonotoneConstraints uarg i = bigAnd $ Map.mapWithKey handlefun $ interpretations i
  where handlefun f p = bigAnd $ map (\n -> getCoeff [Pow (V.Canon n) 1] p .>=. SR.one) $ usablePositions f uarg

monotoneConstraints :: AbstrOrdSemiring a b => PolyInter a -> b
monotoneConstraints i = bigAnd $ Map.mapWithKey handlefun $ interpretations i
  where sig = signature i
        handlefun f p = bigAnd $ map (\n -> getCoeff [Pow (V.Canon n) 1] p .>=. SR.one) [1..F.arity sig f]

safeRedpairConstraints :: AbstrOrdSemiring a b => UsablePositions -> Bool -> PolyInter a -> b
safeRedpairConstraints uarg uaOn i = bigAnd $ Map.mapWithKey handlefun $ compInterpretations i
  where sig = signature i
        compInterpretations = Map.filterWithKey isCompound . interpretations
        isCompound f _ = F.isCompound sig f
        handlefun f p = bigAnd $ map (\n -> getCoeff [Pow (V.Canon n) 1] p .>=. SR.one) $ fposs f
        fposs f = if uaOn then usablePositions f uarg else [1..F.arity sig f]

strictRules :: PolyInter Int -> Trs.Trs -> Trs.Trs
strictRules i = Trs.filterRules $ strictRuleConstraints i

-- instance declarations

class PIEntry a

instance PIEntry Int

instance PIEntry (DioPoly DioVar Int)

instance PIEntry (DioFormula l DioVar Int)

instance PIEntry a => PIEntry (Polynomial V.Variable a)

instance (AbstrEq a b, Semiring a, PIEntry a) => AbstrEq (Polynomial V.Variable a) b where
  (Poly []) .==. (Poly []) = top
  p@(Poly []) .==. q = q .==. p
  p@(Poly (Mono _ vs:_)) .==. q@(Poly _) = (getCoeff vs p .==. getCoeff vs q) && (deleteCoeff vs p .==. deleteCoeff vs q)

instance (AbstrOrd a b, Semiring a, PIEntry a) => AbstrOrd (Polynomial V.Variable a) b where
  p .<. q = (getCoeff [] p .<. getCoeff [] q) && (deleteCoeff [] p .<=. deleteCoeff [] q)
  (Poly []) .<=. (Poly _) = top
  p@(Poly (Mono _ vs:_)) .<=. q@(Poly _) = (getCoeff vs p .<=. getCoeff vs q) && (deleteCoeff vs p .<=. deleteCoeff vs q)

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

instance SatSolver.Decoder (PolyInter (N.Size -> Int)) (N.PLVec DioVar) where
  add (N.PLVec (DioVar y) k) i =  case cast y of
                                    Nothing -> i
                                    Just x -> i{interpretations = Map.adjust newint fun (interpretations i)}
                                      where newint p = case splitFirstCoeff vs p of
                                                         (Nothing, Poly p') -> Poly $ Mono (newval $ const 0) vs:p'
                                                         (Just ov, Poly p') -> Poly $ Mono (newval ov) vs:p'
                                            newval old n = old n + (2 ^ ((if r then 1 else N.bits n) - k))
                                            r   = restrict x
                                            fun = varfun x
                                            vs  = argpos x
