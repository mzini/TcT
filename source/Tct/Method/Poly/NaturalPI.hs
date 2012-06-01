{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# OPTIONS_HADDOCK prune #-}
{- | 
Module      :  Tct.Method.Poly.NaturalPI
Copyright   :  (c) Martin Avanzini <martin.avanzini@uibk.ac.at>, 
               Georg Moser <georg.moser@uibk.ac.at>, 
               Andreas Schnabl <andreas.schnabl@uibk.ac.at>
License     :  LGPL (see COPYING)

Maintainer  :  Andreas Schnabl <andreas.schnabl@uibk.ac.at>
Stability   :  unstable
Portability :  unportable      

This module defines the processor for polynomial interpretations
with natural coefficients.
-}


module Tct.Method.Poly.NaturalPI 
       (
         PolynomialOrder (..)
       , NaturalPI
       , polyProcessor
       ) 
       where

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
import Qlogic.PropositionalFormula (PropAtom)

import qualified Termlib.FunctionSymbol as F
import qualified Termlib.Problem as Prob
import qualified Termlib.Rule as R
import qualified Termlib.Trs as Trs
import Termlib.Utils
import qualified Termlib.Variable as V

import Tct.Certificate (poly, expo, certified, unknown)
import Tct.Encoding.AbstractInterpretation
import Tct.Encoding.Natring ()
import Tct.Encoding.Polynomial as Poly
import Tct.Encoding.UsablePositions hiding (empty, toXml)
import Tct.Method.Poly.PolynomialInterpretation
import Tct.Processor (Answer(..))
import Tct.Processor.Args hiding (toXml)
import qualified Tct.Processor.Args as A
import Tct.Processor.Args.Instances
import Tct.Processor.Orderings
import Tct.Utils.PPrint (indent)
import qualified Tct.Utils.Xml as Xml
import qualified Tct.Processor as P
import qualified Tct.Processor.Standard as S

data PolynomialOrder = 
  PolynomialOrder { ordInter :: PolyInter Int
                  , param    :: PIKind
                  , uargs    :: UsablePositions } deriving Show

data NaturalPI = NaturalPI deriving (Typeable, Show)

instance P.ComplexityProof PolynomialOrder where
  pprintProof order _ = 
      (if uargs order == fullWithSignature (signature $ ordInter order)
       then empty
       else (paragraph "The following argument positions are usable:"
             $+$ indent (pprint (uargs order, signature $ ordInter order))))
      $+$ paragraph ("TcT has computed following " ++ ppknd (param order))
      $+$ pprint (ordInter order)
    where ppknd (UnrestrictedPoly   shp) = ppshp shp
          ppknd (ConstructorBased _ shp) = "constructor-restricted " ++ ppshp shp
          ppshp (SimpleShape s) = show s ++ " polynomial interpretation."
          ppshp (CustomShape _) = "polynomial interpretation." 

  answer order = CertAnswer $ certified (unknown, ub)
    where ub = case knd of 
                 ConstructorBased _ _ -> poly (Just degree)
                 UnrestrictedPoly _ | isStrong && degree <= 1 -> poly (Just 1)
                                    | degree <= 1            -> expo (Just 1)
                                    | otherwise             -> expo (Just 2)
                 
          degree = foldl max 0 [ d |  (f, d) <- degrees pint, consider f ]
            where consider f = 
                    case knd of 
                      ConstructorBased cs _ -> not $ f `Set.member` cs
                      _                     -> True
          
          isStrong = all (all (\ (Mono n _) -> n <= 1)) [ monos | (_,Poly monos) <- inters]
          
          knd      = param order
          pint     = ordInter order
          inters   = Map.toList $ interpretations $ pint

  toXml order = 
    Xml.elt "interpretation" [] (toXml ord par ua)
    where ord = ordInter order
          par = param order
          ua = uargs order

instance S.Processor NaturalPI where
  name NaturalPI = "poly"

  description NaturalPI = [ "This processor orients the problem using polynomial interpretation over natural numbers." ]

  type ArgumentsOf NaturalPI = (Arg (Assoc PolyShape)) :+: (Arg Nat) :+: (Arg (Maybe Nat)) :+: (Arg (Maybe Nat)) :+: (Arg Bool)
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

  type ProofOf NaturalPI = OrientationProof PolynomialOrder

  solve inst prob = orient rs prob (S.processorArgs inst)
       where rs = P.BigAnd [ P.SelectDP (Prob.strictDPs prob)
                           , P.SelectTrs (Prob.strictTrs prob) ]
  solvePartial inst rs prob = mkProof `liftM` orient rs prob (S.processorArgs inst)
       where mkProof res@(Order (PolynomialOrder mi _ _)) = 
               P.PartialProof { P.ppInputProblem = prob
                              , P.ppResult       = res 
                              , P.ppRemovableDPs = Trs.toRules $ strictRules mi $ Prob.dpComponents prob
                              , P.ppRemovableTrs = Trs.toRules $ strictRules mi $ Prob.trsComponents prob }
             mkProof res = 
               P.PartialProof { P.ppInputProblem = prob
                              , P.ppResult       = res
                              , P.ppRemovableDPs = []
                              , P.ppRemovableTrs = [] }

polyProcessor :: S.StdProcessor NaturalPI
polyProcessor = S.StdProcessor NaturalPI

-- argument accessors

kind :: Domains (S.ArgumentsOf NaturalPI) -> Prob.StartTerms -> PIKind
kind args st = kind' (shape args) st
  where kind' shp Prob.TermAlgebra {}    = UnrestrictedPoly shp
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



solveConstraint :: P.SolverM m => 
                    UsablePositions 
                    -> Prob.StartTerms 
                    -> F.Signature 
                    -> Domains (S.ArgumentsOf NaturalPI) 
                    -> DioFormula MiniSatLiteral DioVar Int
                    -> m (S.ProofOf NaturalPI)
solveConstraint ua st sig inst constraints = 
  catchException $ do 
    let fml = toFormula (liftM N.bound cb) (N.bound n) constraints >>= SatSolver.addFormula
        i = abstractInterpretation pk sig :: PolyInter (N.Size -> Int)
    thePI <- P.minisatValue fml i
    return $ case thePI of
      Nothing -> Incompatible
      Just pv -> let pint = fmap (\x -> x n) pv in
                 Order $ PolynomialOrder pint{interpretations = Map.map (unEmpty . shallowSimp) $ interpretations pint} pk ua
  where n      = bound inst
        cb     = cbits inst
        pk     = kind inst st


data PolyDP = PWithDP | PNoDP deriving (Show, Eq)
data Strict = Strict R.Rule deriving (Eq, Ord, Show, Typeable)
instance PropAtom Strict

orient :: P.SolverM m => P.SelectorExpression  -> Prob.Problem -> Domains (S.ArgumentsOf NaturalPI) -> m (S.ProofOf NaturalPI)
orient rs prob args = 
  solveConstraint ua st sig args $
    orientationConstraint
    && dpChoice pdp st uaOn absi

  where ua = usableArgsWhereApplicable (pdp == PWithDP) sig st uaOn strat allrules
        absi = abstractInterpretation pk sig :: PolyInter (DioPoly DioVar Int)
        pdp = if Trs.isEmpty (Prob.strictTrs prob) && Prob.isDPProblem prob
                 then PWithDP
                 else PNoDP     
        sig   = Prob.signature prob
        st    = Prob.startTerms prob
        strat = Prob.strategy prob
        allrules = Prob.allComponents prob  
        pk   = kind args st
        uaOn = isUargsOn args
        orientationConstraint = 
          bigAnd [interpretTerm absi (R.lhs r) .>=. (modify r $ interpretTerm absi (R.rhs r)) | r <- Trs.rules $ allrules]
          && bigOr [strictVar r .>. SR.zero | r <- Trs.rules $ Prob.strictComponents prob]
          && orientSelected rs
          where strictVar = restrictvar . Strict
                modify r (Poly monos) = Poly $ Mono (strictVar r) [] : monos
                orientSelected (P.SelectDP trs) = bigAnd [ strictVar r .>. SR.zero | r <- Trs.rules trs]
                orientSelected (P.SelectTrs trs) = bigAnd [ strictVar r .>. SR.zero | r <- Trs.rules trs]
                orientSelected (P.BigAnd es) = bigAnd [ orientSelected e | e <- es]
                orientSelected (P.BigOr es) = bigOr [ orientSelected e | e <- es]          

        dpChoice PWithDP _                     u     = safeRedpairConstraints ua u
        dpChoice PNoDP   Prob.TermAlgebra {}   _     = monotoneConstraints
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
