{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ParallelListComp #-}
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

import Control.Monad (liftM,foldM)
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
import Qlogic.PropositionalFormula
import Qlogic.SatSolver ((:&:)(..), SatSolver (..))
import qualified Qlogic.MemoizedFormula as MFormula

import qualified Termlib.FunctionSymbol as F
import qualified Termlib.Problem as Prob
import qualified Termlib.Rule as R
import qualified Termlib.Trs as Trs
import qualified Termlib.Term as T
import qualified Termlib.Types as Tpe
import Termlib.Types ((:::)(..))
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
                  
                  } 

data NaturalPI = NaturalPI deriving (Typeable, Show)

instance P.ComplexityProof PolynomialOrder where
  pprintProof order _ = 
      (case knd of 
         TypeBased {} -> 
             paragraph "We consider the following typing:"
              $+$ text "" $+$ indent (pprint (typing knd, sig)) $+$ text ""
         _ -> empty)
      $+$ (if uargs order == fullWithSignature sig
           then empty
           else (paragraph "The following argument positions are considered usable:"
                 $+$ text "" $+$ indent (pprint (uargs order, sig))) $+$ text "")
      $+$ paragraph ("TcT has computed the following " ++ ppknd)
      $+$ text ""
      $+$ pprint inter
      $+$ text ""
      $+$ paragraph "This order satisfies the following ordering constraints."
      $+$ text ""
      $+$ indent (pprintOrientRules inter sig vars rs)      
    where 
      ppknd  = 
          case knd of 
            UnrestrictedPoly {} -> ppshp
            ConstructorBased {} -> "constructor-restricted " ++ ppshp
            TypeBased {} -> "constructor-restricted typed" ++ ppshp
      ppshp = 
          case shape knd of 
            SimpleShape s -> show s ++ " polynomial interpretation."
            CustomShape {} -> "polynomial interpretation." 

      inter = ordInter order
      prob = input order
      knd = param order
      sig = Prob.signature prob
      vars = Prob.variables prob
      rs = [ rl | rl <- Trs.rules $ Prob.allComponents prob 
                , let rt = T.root $ R.lhs rl 
                  in or [ rt == Right f | f <- us ] ]
      us = usymbols order                                            

  answer order = CertAnswer $ C.certified (C.unknown, degree order)

  toXml order = 
    Xml.elt "interpretation" [] (toXml ord par ua)
    where ord = ordInter order
          par = param order
          ua = uargs order

instance S.Processor NaturalPI where
  name NaturalPI = "poly"

  description NaturalPI = [ "This processor orients the problem using polynomial interpretation over natural numbers." ]

  type ArgumentsOf NaturalPI = (Arg PolyShape) :+: (Arg Nat) :+: (Arg (Maybe Nat)) :+: (Arg (Maybe Nat)) :+: (Arg Bool) :+: (Arg Bool) :+: (Arg Bool) :+: (Arg PolyShape) :+: (Arg (Maybe Nat))
  arguments NaturalPI = opt { A.name         = "kind"
                            , A.description  = unwords [ "This argument specifies the shape of the polynomials used in the interpretation."
                                                       , "Allowed values are 'stronglylinear', 'linear', 'simple', 'simplemixed', 'quadratic',"
                                                       , "and 'upto <nat>'"
                                                       , "referring to the respective shapes of the abstract polynomials used." ]
                            , A.defaultValue = SimpleShape Linear }
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
                        opt { A.name        = "cbits"
                            , A.description = unwords [ "This argument specifies the number of bits used for intermediate results, "
                                                      , "as for instance coefficients of matrices obtained by interpreting"
                                                      , "left- and right-hand sides."]
                            , A.defaultValue = Nothing }
                        :+:
                        opt { A.name        = "uargs"
                            , A.description = unwords [ "This argument specifies whether usable arguments are computed (if applicable)"
                                                      , "in order to relax the monotonicity constraints on the interpretation."]
                            , A.defaultValue = True }
                        :+:
                        opt { A.name = "urules"
                            , A.description = unwords [ "This argument specifies whether usable rules modulo argument filtering is applied"
                                                      , "in order to decrease the number of rules that have to be orient. "]
                            , A.defaultValue = True }
                        :+:
                        opt { A.name = "type-based"
                            , A.description = unwords [ "If set, type-based constructor restricted interpretations are used for runtime complexity analysis."
                                                      , "See flag 'constructor-kind' to specify the interpretation shape of constructor symbols, "
                                                      , "and the flag 'degree'." ]
                            , A.defaultValue = True }
                        :+:
                        opt { A.name = "constructor-kind"
                            , A.description = unwords [ "Specifies the shape of interpretations of constructor symbols."
                                                      , "The given shape is automatically restricted so that polynomial bounds can be inferred."
                                                      , "This argument is ignored if the flag 'type-based' is not set."]
                            , A.defaultValue = SimpleShape Linear }
                        :+:
                        opt { A.name        = "degree"
                            , A.description = unwords [ "Specifies an induced upper bound for type-based constructor restricted interpretations."
                                                      , "This argument is ignored if the flag 'type-based' is not set."]
                            , A.defaultValue = Nothing }
                        


  instanceName _ = "polynomial interpretation" -- TODO: show kind (shape $ S.processorArgs inst) ++ 

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

kind :: Domains (S.ArgumentsOf NaturalPI) -> Prob.Problem -> PIKind
kind (shp :+: _ :+: _ :+: _ :+: _  :+: _ :+: True :+: cshp :+: mdeg) prob = 
    case Prob.startTerms prob of 
      (Prob.BasicTerms _ cs) ->
              let types = Tpe.infer (Prob.signature prob) (Trs.toRules (Prob.allComponents prob))
                  (constrTypes, defTypes) = Tpe.partition (\f _ -> f `Set.member` cs) types
                  equivs = Tpe.equivs constrTypes
                  a1 `equiv` a2 = any (\ es -> a1 `elem` es && a2 `elem` es) equivs
              in TypeBased { shape = shp
                           , shapeConstructors = cshp
                           , equivType = equiv
                           , constructorTyping = constrTypes
                           , definedsTyping = defTypes
                           , typing = types
                           , enforcedDegree = mdeg}
      _ -> UnrestrictedPoly shp
kind (shp :+: _ :+: _ :+: _ :+: _  :+: _ :+: False :+: _) prob = 
    case Prob.startTerms prob of 
      (Prob.BasicTerms _ cs) ->
              ConstructorBased { constructors = cs, shape = shp}
      _ -> UnrestrictedPoly shp


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
isUrulesOn (_ :+: _ :+: _ :+: _ :+: _ :+: ur :+: _) = ur

data PolyDP = PWithDP | PNoDP deriving (Show, Eq)
data Strict = Strict R.Rule deriving (Eq, Ord, Show, Typeable)
instance PropAtom Strict

data ValDeg = DegVal (Tpe.Type String) deriving (Eq, Ord, Show, Typeable)
instance PropAtom ValDeg

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
            pform1 <- MFormula.toFormula usableConstraints
            pform2 <- runDio orientConstraints
            pform3 <- N.toFormula typingConstraints
            SatSolver.addFormula (pform1 && pform2 && pform3)
      mpi <- P.minisatValue pform initial
      return $ case mpi of
        Nothing -> Incompatible
        Just o -> Order $ mkOrder o
      
    runDio :: (Ord l, SatSolver.Solver s l) => DioFormula l DioVar Int -> SatSolver s l (PropFormula l)
    runDio = toFormula (N.bound `liftM` cbits args) (N.bound $ bound args)

    mkInter pv = pint {interpretations = Map.map (unEmpty . shallowSimp) $ interpretations pint} 
      where 
        pint = fmap (\x -> x n) pv
        n = bound args
    
    abspi = abstractInterpretation pk sig :: PolyInter (N.Size -> Int)
    
    orientConstraints = 
      monotonicity pdp st uaOn absi
      && bigAnd [ usable r --> interpretTerm absi (R.lhs r) .>=. (modify r $ interpretTerm absi (R.rhs r)) | r <- Trs.rules $ trsrules]
      && bigAnd [ interpretTerm absi (R.lhs r) .>=. (modify r $ interpretTerm absi (R.rhs r)) | r <- Trs.rules $ dprules]      
      && orientSelected rs
      && filteringConstraints
      -- && typingConstraints
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

        monotonicity PWithDP _                     u     = safeRedpairConstraints ua u
        monotonicity PNoDP   Prob.TermAlgebra {}   _     = monotoneConstraints
        monotonicity PNoDP   (Prob.BasicTerms _ _) True  = uargMonotoneConstraints ua
        monotonicity PNoDP   (Prob.BasicTerms _ _) False = monotoneConstraints
        
        filteringConstraints :: (Eq l, Ord l) => DioFormula l DioVar Int
        filteringConstraints  
           | not allowAF = top 
           | otherwise = 
             bigAnd [ bigAnd [ c .>. SR.zero --> bigAnd [ atom (AFEnc.InFilter f i) | Poly.Pow (V.Canon i) _ <- powers ] 
                             | Poly.Mono c powers <- monos ]
                    | (f,Poly.Poly monos) <- Map.toList $ interpretations absi ]

    usableConstraints = MFormula.liftSat $ MFormula.toFormula $ UREnc.validUsableRulesEncoding prob isUnfiltered
      where 
        isUnfiltered f i | allowAF   = AFEnc.isInFilter f i
                         | otherwise = top

    typingConstraints :: (Eq l, Ord l, Monad s, SatSolver.Solver s l) =>  N.NatMonad s l (PropFormula l)
    typingConstraints = 
        case pk of 
          UnrestrictedPoly {} -> top
          ConstructorBased {} -> top
          TypeBased {} -> maybe top enforceDegree (enforcedDegree pk)
                where 
                  enforceDegree :: (Eq l, Ord l, SatSolver.Solver s l) => Nat -> N.NatMonad s l (PropFormula l)
                  enforceDegree (Nat deg) = 
                      bigAnd [ (liftDio $ i .>. SR.zero) -->
                                  (sumPowers powers `mleq` return (natConst deg))
                             | (f ::: decl) <- Tpe.decls (definedsTyping pk)
                             , let Poly monos = typedInterpretation  absi (f ::: decl)
                             , Mono i powers <- monos]
                      && 
                      bigAnd [ (liftDio $ i .>. SR.zero) -->
                                  sumPowers powers `mleq` (return (degValOf otype))
                             | (c ::: decl) <- Tpe.decls (constructorTyping pk) 
                             , let otype = Tpe.outputType decl
                             , let Poly monos = typedInterpretation  absi (c ::: decl) 
                             , Mono i powers <- monos
                             ]
                      where 
                        ma `mleq` mb = do {a <- ma; b <- mb; b `N.mGeq` a}

                        degValOf t = N.natAtom (N.Bound $ max 1 deg) (DegVal t)

                        sumPowers powers = sumM [natConst k `N.mTimesNO` degValOf tv | Pow (_:::tv) k <- powers ]
                            where 
                              sumM ms = sequence ms >>= foldM (\ n a -> n `N.mAdd` a) (natConst 0)
                        

                        natConst = N.natToFormula 
                        
                        liftDio :: Ord l => SatSolver.Solver s l => DioFormula l DioVar Int -> N.NatMonad s l (PropFormula l)
                        liftDio dio = N.liftN (runDio dio)

                          

                         
     

    ua = usableArgsWhereApplicable (pdp == PWithDP) sig st uaOn strat allrules
    absi = abstractInterpretation pk sig :: PolyInter (DioPoly DioVar Int)
    pdp = if Trs.isEmpty (Prob.strictTrs prob) && Prob.isDPProblem prob
          then PWithDP
          else PNoDP     
    allowUR = isUrulesOn args && Prob.isDPProblem prob               
    allowAF = pdp == PWithDP && allowUR
    pk   = kind args prob
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
polynomialInterpretation k = polyProcessor `S.withArgs` (k :+: nat 3 :+: Just (nat 2) :+: Just (nat 3) :+: True :+: True :+: True :+: SimpleShape Linear :+: Nothing)

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

                      
degree :: PolynomialOrder -> C.Complexity
degree order = 
    case knd of 
      ConstructorBased cs _ -> C.poly (Just deg)
          where deg = max' [ d |  (f, d) <- degrees pint, not $ f `Set.member` cs]
      UnrestrictedPoly {}
          | isStrong && deg <= 1 -> C.poly (Just 1)
          | deg <= 1             -> C.expo (Just 1)
          | otherwise            -> C.expo (Just 2)
          where 
            deg = max' [ d |  (_, d) <- degrees pint ]
            isStrong = all (all (\ (Mono n _) -> n <= 1)) [ monos | (_,Poly monos) <- inters]
      TypeBased {} -> C.poly (Just deg)
          where 
            degValue tpe = 
                max' [ degMono monomial 
                     | (c ::: decl) <- Tpe.decls (constructorTyping knd)
                     , Tpe.outputType decl `equiv` tpe
                     , let Poly monos = typedInterpretation  pint (c ::: decl) 
                     , Mono i monomial <- monos, i > 0]
                where 
                  degMono monomial 
                      | any ofTpe monomial = 1
                      | otherwise = sum [ k * degValue tv  | Pow (_::: tv) k <- monomial]
                  ofTpe (Pow (_::: tv) _) = tv `equiv` tpe
            
            equiv = equivType knd

            deg = 
                max' [ sum [ k * degValue tv | Pow (_::: tv) k <- monomial]
                     | (f ::: decl) <- Tpe.decls (definedsTyping knd)
                     , let Poly monos = typedInterpretation  pint (f ::: decl) 
                     , Mono i monomial <- monos, i > 0]

    where 
      knd      = param order
      pint     = ordInter order
      inters   = Map.toList $ interpretations $ pint
      max' = foldl max 0 

