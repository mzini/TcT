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
       , poly
       , simplePolynomial
       , linearPolynomial
       , stronglyLinearPolynomial
       , simpleMixedPolynomial
       , quadraticPolynomial
       , customPolynomial
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
import qualified Qlogic.NatSat as N
import qualified Qlogic.SatSolver as SatSolver
import Qlogic.Semiring
import qualified Qlogic.Semiring as SR
import Qlogic.PropositionalFormula (PropAtom)
import Qlogic.SatSolver ((:&:)(..))
import qualified Qlogic.MemoizedFormula as MFormula

import qualified Termlib.FunctionSymbol as F
import qualified Termlib.Problem as Prob
import qualified Termlib.Rule as R
import qualified Termlib.Trs as Trs
import qualified Termlib.Term as T
import Termlib.Utils
import qualified Termlib.Variable as V
import qualified Termlib.ArgumentFiltering as AF

import qualified Tct.Method.RuleSelector as RS
import qualified Tct.Certificate as C
import Tct.Encoding.AbstractInterpretation
import Tct.Encoding.Natring ()
import Tct.Encoding.Polynomial as Poly
import Tct.Encoding.UsablePositions hiding (empty, toXml)
import qualified Tct.Encoding.UsableRules as UREnc
import qualified Tct.Encoding.ArgumentFiltering as AFEnc

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
                  , uargs    :: UsablePositions 
                  , input    :: Prob.Problem
                  , argFilter :: Maybe AF.ArgumentFiltering
                  , usymbols  :: [F.Symbol]
                  
                  } deriving Show

data NaturalPI = NaturalPI deriving (Typeable, Show)

instance P.ComplexityProof PolynomialOrder where
  pprintProof order _ = 
      (if uargs order == fullWithSignature sig
       then empty
       else (paragraph "The following argument positions are considered usable:"
             $+$ indent (pprint (uargs order, sig))))
      $+$ paragraph ("TcT has computed the following " ++ ppknd (param order))
      $+$ pprint inter
      $+$ text ""
      $+$ paragraph "This order satisfies the following ordering constraints."
      $+$ text ""
      $+$ indent (pprintOrientRules inter sig vars rs)      
    where 
      ppknd (UnrestrictedPoly   shp) = ppshp shp
      ppknd (ConstructorBased _ shp) = "constructor-restricted " ++ ppshp shp
      ppshp (SimpleShape s) = show s ++ " polynomial interpretation."
      ppshp (CustomShape _) = "polynomial interpretation." 

      inter = ordInter order
      prob = input order
      sig = Prob.signature prob
      vars = Prob.variables prob
      rs = [ rl | rl <- Trs.rules $ Prob.allComponents prob 
                , let rt = T.root $ R.lhs rl 
                  in or [ rt == Right f | f <- us ] ]
      us = usymbols order                                            

  answer order = CertAnswer $ C.certified (C.unknown, ub)
    where ub = case knd of 
                 ConstructorBased _ _ -> C.poly (Just degree)
                 UnrestrictedPoly _ | isStrong && degree <= 1 -> C.poly (Just 1)
                                    | degree <= 1            -> C.expo (Just 1)
                                    | otherwise             -> C.expo (Just 2)
                 
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

  type ArgumentsOf NaturalPI = (Arg (Assoc PolyShape)) :+: (Arg Nat) :+: (Arg (Maybe Nat)) :+: (Arg (Maybe Nat)) :+: (Arg Bool) :+: (Arg Bool)
  arguments NaturalPI = opt { A.name         = "kind"
                            , A.description  = unlines [ "This argument specifies the shape of the polynomials used in the interpretation."
                                                       , "Allowed values are 'stronglylinear', 'linear', 'simple', 'simplemixed', and 'quadratic',"
                                                       , "referring to the respective shapes of the abstract polynomials used." ]
                            , A.defaultValue = SimpleShape Linear }
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
                        :+:
                        opt { A.name = "urules"
                            , A.description = unwords [ "This argument specifies whether usable rules modulo argument filtering is applied"
                                                      , "in order to decreas the number of rules to orient. "]
                            , A.defaultValue = True }

  instanceName inst = show (shape $ S.processorArgs inst) ++ " polynomial interpretation"

  type ProofOf NaturalPI = OrientationProof PolynomialOrder

  solve inst prob = orient rs prob (S.processorArgs inst)
       where rs = RS.rsSelect (RS.selAllOf RS.selStricts) prob  
  solvePartial inst rs prob = mkProof `liftM` orient rs prob (S.processorArgs inst)
       where 
         mkProof res@(Order ord@(PolynomialOrder {})) = 
           P.PartialProof { P.ppInputProblem = prob
                          , P.ppResult       = res 
                          , P.ppRemovableDPs = Trs.toRules $ strictRules inter $ Prob.dpComponents prob
                          , P.ppRemovableTrs = Trs.toRules $ strictRules inter $ Prob.trsComponents prob }
           where inter = ordInter ord
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
isUargsOn (_ :+: _ :+: _ :+: _ :+: ua :+: _) = ua

isUrulesOn :: Domains (S.ArgumentsOf NaturalPI) -> Bool
isUrulesOn (_ :+: _ :+: _ :+: _ :+: _ :+: ur) = ur

data PolyDP = PWithDP | PNoDP deriving (Show, Eq)
data Strict = Strict R.Rule deriving (Eq, Ord, Show, Typeable)
instance PropAtom Strict

orient :: P.SolverM m => P.SelectorExpression  -> Prob.Problem -> Domains (S.ArgumentsOf NaturalPI) -> m (S.ProofOf NaturalPI)
orient rs prob args = catchException $ do 
  case pdp of 
    PWithDP -> solve initial mkOrder 
      where 
        mkOrder (pv :&: af :&: us) = 
          PolynomialOrder { ordInter = mkInter pv
                          , param = pk 
                          , uargs = ua 
                          , input = prob
                          , argFilter = if allowAF then Just af else Nothing
                          , usymbols = us }
        initial = abspi :&: AFEnc.initial sig :&: UREnc.initialUsables prob
      
    PNoDP -> solve abspi mkOrder 
      where 
        mkOrder pv = 
          PolynomialOrder { ordInter = mkInter pv
                          , param = pk 
                          , uargs = ua 
                          , input = prob
                          , argFilter = Nothing
                          , usymbols = Set.toList $ Trs.definedSymbols $ Prob.trsComponents prob }

  where 
    solve :: (SatSolver.Decoder e a, P.SolverM m) => e -> ( e -> PolynomialOrder) -> m (OrientationProof PolynomialOrder)
    solve initial mkOrder = do 
      let pform = do
            pform1 <- MFormula.toFormula mconstraints
            pform2 <- toFormula (N.bound `liftM` cbits args) (N.bound $ bound args) dconstraints
            SatSolver.addFormula (pform1 && pform2)
      mpi <- P.minisatValue pform initial
      return $ case mpi of
        Nothing -> Incompatible
        Just o -> Order $ mkOrder o
      
    mkInter pv = pint {interpretations = Map.map (unEmpty . shallowSimp) $ interpretations pint} 
      where 
        pint = fmap (\x -> x n) pv
        n = bound args
    
    abspi = abstractInterpretation pk sig :: PolyInter (N.Size -> Int)
    
    dconstraints = 
      dpChoice pdp st uaOn absi
      && bigAnd [ usable r --> interpretTerm absi (R.lhs r) .>=. (modify r $ interpretTerm absi (R.rhs r)) | r <- Trs.rules $ trsrules]
      && bigAnd [ interpretTerm absi (R.lhs r) .>=. (modify r $ interpretTerm absi (R.rhs r)) | r <- Trs.rules $ dprules]      
      && orientSelected rs
      && filteringConstraints
      where 
        usable 
          | allowUR = UREnc.usable prob
          | otherwise = const top
        strictVar = restrictvar . Strict
        modify r (Poly monos) = Poly $ Mono (strictVar r) [] : monos
        orientSelected (P.SelectDP r) = strictVar r .>. SR.zero
        orientSelected (P.SelectTrs r) = strictVar r .>. SR.zero
        orientSelected (P.BigAnd es) = bigAnd [ orientSelected e | e <- es]
        orientSelected (P.BigOr es) = bigOr [ orientSelected e | e <- es]          

        dpChoice PWithDP _                     u     = safeRedpairConstraints ua u
        dpChoice PNoDP   Prob.TermAlgebra {}   _     = monotoneConstraints
        dpChoice PNoDP   (Prob.BasicTerms _ _) True  = uargMonotoneConstraints ua
        dpChoice PNoDP   (Prob.BasicTerms _ _) False = monotoneConstraints
        
        filteringConstraints :: (Eq l, Ord l) => DioFormula l DioVar Int
        filteringConstraints  
           | not allowAF = top 
           | otherwise = 
             bigAnd [ bigAnd [ c .>. SR.zero --> bigAnd [ atom (AFEnc.InFilter f i) | Poly.Pow (V.Canon i) _ <- powers ] 
                             | Poly.Mono c powers <- monos ]
                    | (f,Poly.Poly monos) <- Map.toList $ interpretations absi ]
    mconstraints = MFormula.liftSat $ MFormula.toFormula $ UREnc.validUsableRulesEncoding prob isUnfiltered
      where 
        isUnfiltered f i | allowAF   = AFEnc.isInFilter f i
                         | otherwise = top
                         
    
    ua = usableArgsWhereApplicable (pdp == PWithDP) sig st uaOn strat allrules
    absi = abstractInterpretation pk sig :: PolyInter (DioPoly DioVar Int)
    pdp = if Trs.isEmpty (Prob.strictTrs prob) && Prob.isDPProblem prob
          then PWithDP
          else PNoDP     
    allowUR = isUrulesOn args && Prob.isDPProblem prob               
    allowAF = pdp == PWithDP && allowUR
    pk   = kind args st
    uaOn = isUargsOn args
    
    sig   = Prob.signature prob
    st    = Prob.startTerms prob
    strat = Prob.strategy prob
    allrules = Prob.allComponents prob  
    dprules  = Prob.dpComponents prob  
    trsrules = Prob.trsComponents prob  

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

-- | This processor implements polynomial interpretations.
polynomialInterpretation :: PolyShape -> S.ProcessorInstance NaturalPI
polynomialInterpretation k = polyProcessor `S.withArgs` (k :+: nat 3 :+: Just (nat 2) :+: Just (nat 3) :+: True :+: True)

poly :: S.ProcessorInstance NaturalPI
poly =  simplePolynomial 

-- | Options for @simple@ polynomial interpretations.
simplePolynomial :: S.ProcessorInstance NaturalPI
simplePolynomial =  polynomialInterpretation $ SimpleShape Simple

-- | Options for @linear@ polynomial interpretations.
linearPolynomial :: S.ProcessorInstance NaturalPI
linearPolynomial = polynomialInterpretation $ SimpleShape Linear

-- | Options for @strongly linear@ polynomial interpretations.
stronglyLinearPolynomial :: S.ProcessorInstance NaturalPI
stronglyLinearPolynomial = polynomialInterpretation $ SimpleShape StronglyLinear

-- | Options for @simple mixed@ polynomial interpretations.
simpleMixedPolynomial :: S.ProcessorInstance NaturalPI
simpleMixedPolynomial = polynomialInterpretation $ SimpleShape SimpleMixed

-- | Options for @quadratic mixed@ polynomial interpretations.
quadraticPolynomial :: S.ProcessorInstance NaturalPI
quadraticPolynomial = polynomialInterpretation $ SimpleShape Quadratic

-- | Option for polynomials of custom shape, as defined by the first argument.
-- This function receives a list of variables 
-- denoting the @n@ arguments of the interpretation function. The return value of type ['SimpleMonomial']
-- corresponds to the list of monomials of the constructed interpretation function.
-- A polynomial is a list of unique 'SimpleMonomial', where 'SimpleMonomial' are 
-- considered equal if the set variables together with powers match.
-- 'SimpleMonomial' can be build using '^^^', 'constant' and 'mono'.
-- For instance, linear interpretations are constructed using the function 
-- @ 
-- \vs -> [constant] ++ [ v^^^1 | v <- vs]
-- @
-- . 
customPolynomial :: ([V.Variable] -> [SimpleMonomial]) -> S.ProcessorInstance NaturalPI
customPolynomial mk = polynomialInterpretation $ CustomShape mk
