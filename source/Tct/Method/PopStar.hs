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

{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}

module Tct.Method.PopStar 
    ( popstarProcessor
    , ppopstarProcessor
    , lmpoProcessor
    , popstar
    , lmpo
    , popstarPS
    , popstarSmall
    , popstarSmallPS
    , PopStarOrder (..)
    , PopStar)
where

import Control.Monad (liftM)
import Data.Set (Set, (\\))
import Data.Maybe (isJust)
import qualified Data.Set as Set
import qualified Data.Map as Map
import Data.Typeable
import Prelude hiding ((&&),(||),not)
import qualified Text.PrettyPrint.HughesPJ as PP
import Text.PrettyPrint.HughesPJ hiding (empty)

import Qlogic.Boolean
import Qlogic.MemoizedFormula
import Qlogic.MiniSat
import Qlogic.PropositionalFormula
import Qlogic.SatSolver ((:&:) (..), addFormula)
import qualified Qlogic.SatSolver as S

import Termlib.FunctionSymbol (Symbol, isMarked)
import Termlib.Problem (StartTerms(..), Strategy(..), Problem(..))
import Termlib.Rule (lhs, rhs, Rule)
-- import Termlib.Signature (runSignature)
import Termlib.Term
import Termlib.Trs (Trs, rules)
import Termlib.Utils (PrettyPrintable(..), ($++$), block)
import qualified Termlib.ArgumentFiltering as AF
import qualified Termlib.Precedence as Prec
import qualified Termlib.Problem as Prob
import qualified Termlib.Trs as Trs

import Tct.Certificate (poly, expo, certified, unknown)
import qualified Tct.Processor.Standard as S
import qualified Tct.Processor as P
import Tct.Processor (ComplexityProof(..), Answer (..))
import Tct.Processor.Orderings
import Tct.Processor.Args
import Tct.Processor.Args.Instances (nat, natToInt, Nat(..))
import qualified Tct.Processor.Args as A
import Tct.Encoding.Relative hiding (trs)
import qualified Tct.Encoding.ArgumentFiltering as AFEnc
import qualified Tct.Encoding.UsableRules as UREnc
import qualified Tct.Encoding.Precedence as PrecEnc
-- import qualified Tct.Encoding.Relative as Rel
import qualified Tct.Encoding.SafeMapping as SMEnc


--------------------------------------------------------------------------------
--- proof object

data OrdType = POP | ProdPOP | LMPO deriving (Typeable, Show, Eq)

data PopStar = PopStar { kind :: OrdType } deriving (Typeable, Show)


data PopStarOrder = PopOrder { popSafeMapping       :: SMEnc.SafeMapping
                             , popPrecedence        :: Prec.Precedence
                             , popRecursives        :: PrecEnc.RecursiveSymbols
                             , popArgumentFiltering :: Maybe AF.ArgumentFiltering
                             , popInputProblem      :: Problem
                             , popInstance          :: S.TheProcessor PopStar
                             , popUsableSymbols     :: [Symbol]}

instance ComplexityProof PopStarOrder where
  pprintProof order _ = (text "The input was oriented with the instance of" <+> text (S.instanceName inst) <+> text "as induced by the precedence")
                        $++$ pparam (popPrecedence order)
                        $++$ text "and safe mapping"
                        $++$ pparam (popSafeMapping order) <+> text "."
                        $+$ (case maf of 
                               Nothing -> PP.empty
                               Just af -> text "" 
                                         $+$ text "Further, following argument filtering is employed:"
                                         $++$ pparam af
                                         $++$ text "Usable defined function symbols are a subset of:"
                                         $++$ pparam (braces $ fsep $ punctuate (text ",")  [pprint (f,sig) | f <- us]))
                        $++$ text "For your convenience, here is the oriented problem in predicative notation:"
                        $++$ pparam ppProblem
      where pparam :: PrettyPrintable p => p -> Doc 
            pparam = nest 1 . pprint
            inst = popInstance order
            ppProblem = ppTrs     "Strict DPs"   strictDPs prob
                        $+$ ppTrs "Weak DPs  "   weakDPs   prob
                        $+$ ppTrs "Strict Trs"   (restrictUsables . strictTrs) prob
                        $+$ ppTrs "Weak Trs  "   (restrictUsables . weakTrs)   prob

            ppTrs n f p = block n $ pprint (f p, sig, vars,sm)
            prob           = popInputProblem order
            sig            = Prob.signature prob
            vars           = Prob.variables prob
            sm             = popSafeMapping order
            us             = popUsableSymbols order
            maf            = popArgumentFiltering order
            restrictUsables trs | isJust maf = Trs.filterRules 
                                               (\ rl -> case root (lhs rl) of 
                                                   Right f -> f `elem` us
                                                   Left _  -> True) trs
                                | otherwise  = trs
                             

  answer order = case kind $ S.processor inst of 
                   LMPO    -> CertAnswer $ certified (unknown, expo Nothing)
                   POP     -> CertAnswer $ certified (unknown, poly Nothing)
                   ProdPOP | wsc       -> CertAnswer $ certified (unknown, poly $ Just ub) 
                           | otherwise -> CertAnswer $ certified (unknown, poly Nothing)
      where inst       = popInstance order
            _ :+: wsc :+: _ = S.processorArgs inst
            ub              = maximum (minUb : Map.elems (Prec.recursionDepth rs prec))
            (PrecEnc.RS rs) = popRecursives order
            prec            = popPrecedence order
            minUb           = 
              case popArgumentFiltering order of 
                Just af -> if hasProjection af then 1 else 0
                Nothing -> 0
            sig = Prob.signature $ popInputProblem order
            hasProjection af = AF.fold (\ sym filtering -> (||) (f sym filtering)) af False
              where f sym (AF.Projection _) | isMarked sig sym = True
                                            | otherwise        = False
                    f _ _                                      = False

--------------------------------------------------------------------------------
--- processor 

instance S.Processor PopStar where
    name p = case kind p of 
               LMPO    -> "lmpo"
               POP     -> "pop*"
               ProdPOP -> "ppop*"

    description p = case kind p of 
                      LMPO -> [ unlines [ "This processor implements orientation of the input problem using 'light multiset path orders',"
                                       , "a technique applicable for innermost runtime-complexity analysis."
                                       , "Light multiset path orders are a miniaturisation of 'multiset path orders',"
                                       , "restricted so that compatibility assesses polytime computability of the functions defined, "
                                       , "cf. http://www.loria.fr/~marionjy/Papers/icc99.ps ."
                                       , "Further, it induces exponentially bounded innermost runtime-complexity."]]
                      POP   -> [ unlines [ "This processor implements orientation of the input problem using 'polynomial path orders',"
                                        , "a technique applicable for innermost runtime-complexity analysis."
                                        , "Polynomial path orders are a miniaturisation of 'multiset path orders',"
                                        , "restricted so that compatibility assesses a polynomial bound on the innermost runtime-complexity, "
                                        , "cf. http://cl-informatik.uibk.ac.at/~zini/publications/FLOPS08.pdf ."]
                              , unlines [ "The implementation for the WDP-setting follows closely"
                                        , "http://cl-informatik.uibk.ac.at/~zini/publications/RTA09.pdf ,"
                                        , "where addionally argument filterings are employed." ]]
                      ProdPOP -> [ unlines [ "This processor implements orientation of the input problem using 'polynomial path orders'"
                                          , "with product extension, c.f. processor 'pop*'"]]


    type S.ArgumentsOf PopStar = Arg Bool :+: Arg Bool :+: Arg (Maybe Nat)

    instanceName inst = show $ ppname <+> ppargs
        where ppname = case kind $ S.processor inst of 
                         LMPO -> text "Lightweight Multiset Path Order"
                         POP -> text "Polynomial Path Order"
                         ProdPOP -> text "Polynomial Path Order (product extension)"

              ppargs | ps && wsc = text "with parameter subtitution and weak safe composition"
                     | ps        = text "with parameter subtitution"
                     | wsc       = text "with weak safe composition"
                     | otherwise = PP.empty
              ps :+: wsc :+: _ = S.processorArgs inst

    arguments _ = ps :+: wsc :+: bnd
        where ps = opt { A.name = "ps"
                       , A.description = unlines [ "If enabled then the scheme of parameter substitution is admitted,"
                                                 , "cf. http://cl-informatik.uibk.ac.at/~zini/publications/WST09.pdf how this is done for polynomial path orders." ]
                       , A.defaultValue = True } 
              wsc = opt { A.name = "wsc"
                        , A.description = unlines [ "If enabled then composition is restricted to weak safe composition,"
                                                  , "compare http://cl-informatik.uibk.ac.at/~zini/publications/WST10.pdf." ]
                        , A.defaultValue = False }
              bnd = opt { A.name = "ub"
                        , A.description = unlines [ "If enabled then composition is restricted to weak safe composition,"
                                                  , "compare http://cl-informatik.uibk.ac.at/~zini/publications/WST10.pdf." ]
                        , A.defaultValue = Nothing }
                  

    type S.ProofOf PopStar = OrientationProof PopStarOrder
    solve inst prob = case (Prob.startTerms prob, Prob.strategy prob) of 
                     ((BasicTerms _ _), Innermost) -> orientProblem inst prob
                     _                             -> return (Inapplicable "Processor only applicable for innermost runtime complexity analysis")



popstarProcessor :: S.StdProcessor PopStar
popstarProcessor = S.StdProcessor (PopStar POP)

ppopstarProcessor :: S.StdProcessor PopStar
ppopstarProcessor = S.StdProcessor (PopStar ProdPOP)

lmpoProcessor :: S.StdProcessor PopStar
lmpoProcessor = S.StdProcessor (PopStar LMPO)

popstar :: P.InstanceOf (S.StdProcessor PopStar)
popstar = popstarProcessor `S.withArgs` (False :+: False :+: Nothing)

lmpo :: P.InstanceOf (S.StdProcessor PopStar)
lmpo = lmpoProcessor `S.withArgs` (False :+: False :+: Nothing)

popstarPS :: P.InstanceOf (S.StdProcessor PopStar)
popstarPS = popstarProcessor `S.withArgs` (True :+: False :+: Nothing)

popstarSmall :: Maybe Int -> P.InstanceOf (S.StdProcessor PopStar)
popstarSmall mi = ppopstarProcessor `S.withArgs` (False :+: True :+: (nat `liftM` mi))

popstarSmallPS :: Maybe Int -> P.InstanceOf (S.StdProcessor PopStar)
popstarSmallPS mi = ppopstarProcessor `S.withArgs` (True :+: True :+: (nat `liftM` mi))



--------------------------------------------------------------------------------
-- encoding

quasiConstructorsFor :: Problem -> Set Symbol
quasiConstructorsFor prob = constructors
                            `Set.union` (quasiConstructors $ Prob.allComponents prob)
    where quasiConstructors rs = Set.unions [qd (lhs r) | r <- rules rs ]
          qd (Fun _ ts) = Set.unions [ functionSymbols t | t <- ts] 
          qd _          = error "Method.PopStar: non-trs given"
          constructors = case Prob.startTerms prob of 
            BasicTerms _ cs -> cs
            _               -> Set.empty



data Predicates l = Predicates {
      definedP      :: Symbol -> PropFormula l
    , collapsingP   :: Symbol -> PropFormula l
    , inFilterP     :: Symbol -> Int -> PropFormula l
    , safeP         :: Symbol -> Int -> PropFormula l
    , precGtP       :: Symbol -> Symbol -> PropFormula l
    , precEqP       :: Symbol -> Symbol -> PropFormula l
    , allowMulRecP  :: PropFormula l
    , allowPsP      :: PropFormula l
    , weakSafeCompP :: PropFormula l
    , prodExtP      :: PropFormula l
  }

data PopArg = Gt Term Term
            | Gsq Term Term
            | Eq Term Term
              deriving (Eq, Ord, Show)


orientProblem :: P.SolverM m => S.TheProcessor PopStar -> Problem -> m (OrientationProof PopStarOrder)
orientProblem inst prob = maybe Incompatible Order `liftM` slv 
                                    
    where knd = kind $ S.processor inst
          allowPS :+: forceWSC :+: bnd = S.processorArgs inst
          allowAF   = (isDP && knd /= LMPO)
          allowMR   = knd == LMPO 
          forcePROD = knd == ProdPOP          
          isDP      = Prob.isDPProblem prob && Trs.isEmpty (Prob.strictTrs prob)
          quasiConstrs = quasiConstructorsFor prob
          quasiDefineds = Trs.definedSymbols allrules \\ quasiConstrs
          strs     = Prob.strictTrs prob
          wtrs     = Prob.weakTrs prob
          sdps     = Prob.strictDPs prob
          wdps     = Prob.weakDPs prob
          stricts  = Prob.strictComponents prob
          weaks    = Prob.weakComponents prob
          allrules = Prob.allComponents prob
          sig      = Prob.signature prob

          slv | isDP      = solveDP 
              | otherwise = solveDirect
          
          solveDP = solveConstraint form initial mkOrd
              where mkOrd (us :&: sm :&: rs :&: prec :&: af) = PopOrder { popSafeMapping       = sm
                                                                        , popPrecedence        = prec
                                                                        , popRecursives        = rs
                                                                        , popArgumentFiltering = Just af 
                                                                        , popInputProblem      = prob 
                                                                        , popInstance          = inst 
                                                                        , popUsableSymbols     = us }
                    initial                            = UREnc.initialUsables 
                                                         :&: SMEnc.empty sig quasiConstrs 
                                                         :&: PrecEnc.initialRecursiveSymbols                                                         
                                                         :&: PrecEnc.initial sig 
                                                         :&: AFEnc.initial sig

          solveDirect = solveConstraint form initial mkOrd
              where mkOrd (sm :&: rs :&: prec) = PopOrder { popSafeMapping       = sm
                                                          , popPrecedence        = prec
                                                          , popRecursives        = rs
                                                          , popArgumentFiltering = Nothing
                                                          , popInputProblem      = prob 
                                                          , popInstance          = inst 
                                                          , popUsableSymbols     = Set.toList $ Trs.definedSymbols $ Prob.trsComponents prob }
                    initial             = SMEnc.empty sig quasiConstrs 
                                          :&: PrecEnc.initialRecursiveSymbols
                                          :&: PrecEnc.initial sig

          solveConstraint :: (S.Decoder e a) => P.SolverM m => MemoFormula PopArg MiniSatSolver MiniSatLiteral -> e -> (e -> b) -> m (Maybe b)
          solveConstraint constraint initial makeResult = 
              do r <- P.minisatValue (toFormula constraint >>= addFormula) initial
                 return $ makeResult `liftM` r
          
          form = fm maybeOrientable 
                 && bigAnd [atom (strictlyOriented r) | r <- rules $ sdps]
                 && bigAnd [atom (weaklyOriented r)   | r <- rules $ wdps]                 
                 && bigAnd [not (usable r) || atom (strictlyOriented r) | r <- rules $ strs]
                 && bigAnd [not (usable r) || atom (weaklyOriented r)   | r <- rules $ wtrs]
                 && validPrecedence
                 && (fm allowAF --> validArgumentFiltering)
                 && (fm isDP --> validUsableRules)
                 && orderingConstraints allowAF allowMR allowPS forceWSC forcePROD stricts weaks quasiDefineds

          usable r = return $ UREnc.usable r
          maybeOrientable = allowMR || isDP || (all maybeOrientableRule $ rules allrules)
            where maybeOrientableRule r = 
                      case rtl of 
                        Left  _   -> False 
                        Right sym -> sym `Set.member` quasiDefineds --> cardinality rtl (rhs r) <= 1
                      where rtl = root (lhs r)
          
          validArgumentFiltering = return $ 
                                   AFEnc.validSafeArgumentFiltering fs sig
                                   && (case bnd of 
                                         Just (Nat 0) -> bigAnd [ not (AFEnc.isCollapsing f) | f <- fs, isMarked sig f]
                                         _            -> top)
            where fs = Set.toList $ Trs.functionSymbols allrules
          
          validPrecedence        = liftSat $ PrecEnc.validPrecedenceM (Set.toList quasiDefineds) (natToInt `liftM` bnd)
          
          validUsableRules = liftSat $ toFormula $ UREnc.validUsableRulesEncoding prob isUnfiltered                    
            where isUnfiltered f i | allowAF   = AFEnc.isInFilter f i
                                   | otherwise = top
                                                 
orderingConstraints :: (S.Solver s l, Eq l, Show l, Ord l) => Bool -> Bool -> Bool -> Bool -> Bool -> Trs -> Trs -> Set Symbol -> MemoFormula PopArg s l
orderingConstraints allowAF allowMR allowPS forceWSC forcePROD strict weak quasiDefineds = 
    strict `orientStrictBy` pop && weak `orientWeakBy` popEq
    where orientBy ob trs ord = bigAnd [atom (ob r) --> lhs r `ord` rhs r | r <- rules trs]
          orientStrictBy = orientBy strictlyOriented 
          orientWeakBy = orientBy weaklyOriented
          pop s t             = orient preds (Gt s t)
          popEq s t           = orient preds (Eq s t) || orient preds (Gt s t)
          preds               = Predicates {
                                definedP    = defP
                                , collapsingP   = if allowAF then AFEnc.isCollapsing else const bot
                                , inFilterP     = if allowAF then AFEnc.isInFilter else const . const top
                                , safeP         = \ f i -> not (defP f) || SMEnc.isSafeP f i
                                , precGtP       = \ f g -> defP f && (not (defP g) || f `PrecEnc.precGt` g)
                                , precEqP       = \ f g -> (not (defP f) && not (defP g)) || (defP f && defP g && f `PrecEnc.precEq` g)
                                , allowMulRecP  = fm allowMR
                                , allowPsP      = fm allowPS
                                , weakSafeCompP = fm forceWSC
                                , prodExtP      = fm forcePROD
                              } where defP f = fm $ f `Set.member` quasiDefineds


newtype AlphaAtom   = Alpha   (Int, (Term, Term))      deriving (Eq, Ord, Typeable, Show)
newtype DeltaAtom   = Delta   (Int, Int, (Term, Term)) deriving (Eq, Ord, Typeable, Show)
newtype EpsilonAtom = Epsilon (Int, (Term, Term))      deriving (Eq, Ord, Typeable, Show)
newtype GammaAtom   = Gamma   (Int, Int, (Term, Term)) deriving (Eq, Ord, Typeable, Show)

instance PropAtom AlphaAtom
instance PropAtom DeltaAtom
instance PropAtom EpsilonAtom
instance PropAtom GammaAtom

orient :: (S.Solver s l, Eq l, Show l) => Predicates l -> (PopArg -> MemoFormula PopArg s l)
orient p = memoized $ \ a -> 
           case a of 
             Gt (Var _)      _  -> bot
             Gt s@(Fun f ss) t -> case1 || case2 || case3   
                 where iss = indexed ss 
                       case1 = not (isCollapsing f) && bigOr [inFilter f i && (s_i `equiv` t) | (s_i, i) <- iss]
                       case2 = bigOr [inFilter f i && s_i `gpop` t | (s_i, i) <- iss]
                       case3 = case t of 
                                 (Var _)    -> bot
                                 (Fun g []) -> not (isCollapsing f) && f `pGt` g
                                 (Fun g ts) -> not (isCollapsing f) 
                                              && forall its (\ (t_j, j) -> 
                                                       inFilter g j 
                                                       --> bigAnd [ isCollapsing g 
                                                                    || (isDefined f 
                                                                       && (not (f `pGt` g) || isSafe g j || s `gsq` t_j)
                                                                       && bigOr [ isNormal g j
                                                                               , precRestrictedP f t_j
                                                                               , f `pGt` g && alpha j])
                                                                  , s `gpop` t_j || not (isCollapsing g) && isNormal g j])
                                              && (isCollapsing g 
                                                  || (f `pGt` g && (mulRecForbidden --> atmostOne [alpha j | (_,j) <- its]))
                                                  || (f `pEq` g && isRecursive f && isRecursive g && isDefined f && seqExtGt))
                                     where seqExtGt = -- every position j of rhs is covered:
                                                      -- for ps, only cover of normal args of rhs required
                                                      forall js (\ j -> (inFilter g j && (not ps || isNormal g j)) -- for ps, only constraint on normal args
                                                                   --> exist is (\ i -> gamma i j))
                                                      -- if ps, cover only on by normal argument positions of rhs
                                                      && (ps --> (forall is (\ i -> (exist js (\ j -> gamma i j)) --> inFilter f i && isNormal f i)))
                                                      -- if one of following holds then s_i covers single t_j:
                                                      --   s_i = t_j (i.e. epsilon i)
                                                      --   product extension is used and in case of ps i is normal arg pos
                                                      && forall is (\ i -> 
                                                              (epsilon i || (pext && (not ps || isNormal f i))) --> exactlyOne [gamma i j | j <- js])
                                                      -- there exists a strict decrease in the rhs
                                                      && exist is (\ i -> not (epsilon i) && isNormal f i && inFilter f i)
                                                      -- and finally the recursive ordering constraints
                                                      && forall iss (\ (s_i, i) -> 
                                                               forall its (\ (t_j, j) -> 
                                                                      gamma i j 
                                                                      --> bigAnd [ inFilter f i
                                                                                 , ite ps (isNormal f i) (isSafe f i <-> isSafe g j)
                                                                                 , ite (epsilon i) (s_i `equiv` t_j) (s_i `gpop` t_j) ]))
                                           its = indexed ts
                                           is  = [ i | (_, i) <- iss ]
                                           js  = [ j | (_, j) <- its ]
                                           alpha j     = return $ propAtom $ Alpha (j, (s, t))
                                           gamma i j   = return $ propAtom $ Gamma (i, j, (s, t))
                                           epsilon i   = return $ propAtom $ Epsilon (i, (s, t))
                                           isNormal f' i = not (isSafe f' i)
                                           isRecursive = return . PrecEnc.isRecursive
                                           mulRecForbidden = return $ not (allowMulRecP p)
                                           ps = return $ allowPsP p
                                           precRestrictedP _ (Var _)    = top
                                           precRestrictedP f' (Fun g' ts') = f' `pGt` g' && bigAnd [ inFilter g' j --> precRestrictedP f' t_j  
                                                                                               | (t_j,j) <- indexed ts']

             Gsq  (Var _)      _ -> bot
             Gsq  s@(Fun f ss) t -> case2 || case1 || case3
                 where iss = indexed ss 
                       fWhenDefinedNormal pos = isDefined f --> not (isSafe f pos)
                       tNonCollapsingOrVar = case t of {Var _ -> top; Fun g _ ->  not (isCollapsing g)}
                       case1 = bigOr [ (not (isCollapsing f) --> fWhenDefinedNormal i && tNonCollapsingOrVar)
                                   && inFilter f i
                                   && s_i `gsq` t 
                                   | (s_i, i) <- iss]
                       case2 = tNonCollapsingOrVar && not (isCollapsing f) 
                               && bigOr [ (s_i `equiv` t) && fWhenDefinedNormal i && inFilter f i | (s_i,i) <- iss]
                       case3 = not wsc && case t of 
                                            (Fun g ts) -> not (isCollapsing f) 
                                                          && (isCollapsing g || (isDefined f && f `pGt` g))
                                                         && bigAnd [inFilter g j --> s `gsq` t_j | (t_j, j) <- indexed ts] 
                                            _          -> bot

             Eq (Var v1)     (Var v2)     -> fm $ v1 == v2
             Eq v@(Var _)    t@(Fun _ _)  -> t `equiv` v
             Eq (Fun f us)   v@(Var _)    -> isCollapsing f && (forall (indexed us) $ \ (ui,i) -> inFilter f i --> v `equiv` ui)
             Eq s@(Fun f ss) t@(Fun g ts) -> fm (s == t) || (ite (isCollapsing f) 
                                                                (equivCollaps f iss t) 
                                                                (ite (isCollapsing g) 
                                                                     (equivCollaps g its s) 
                                                                     equivNonCollaps))
                 where (iss, its) = (indexed ss, indexed ts)
                       is = [i | (_,i) <- iss]
                       js = [j | (_,j) <- its] 
                       delta i j               = return $ propAtom $ Delta (i, j, (s, t))
                       equivCollaps f' ius w   = bigAnd [ inFilter f' i --> u_i `equiv` w | (u_i,i) <- ius ]
                       equivNonCollaps         = f `pEq` g
                                                 && encodeDelta 
                                                 && (forall iss $ \ (s_i,i) -> 
                                                         forall its $ \ (t_j, j) -> 
                                                             delta i j --> bigAnd [ inFilter f i
                                                                           , inFilter g j 
                                                                           , isSafe f i <-> isSafe g j
                                                                           , s_i `equiv` t_j])
                       encodeDelta             = ( forall is $ \ i -> inFilter f i --> exactlyOne [delta i j | j <- js])
                                                 && ( forall js $ \ j -> inFilter g j --> exactlyOne [delta i j | i <- is])


    where s `gpop` t = orient p (Gt s t)
          s `gsq`  t = orient p (Gsq s t)
          s `equiv` t      = orient p (Eq s t)
          pGt f g          = return $ precGtP p f g
          pEq f g          = return $ precEqP p f g
          inFilter f i     = return $ inFilterP p f i
          isSafe f i       = return $ safeP p f i
          isCollapsing f   = return $ collapsingP p f
          isDefined f      = return $ definedP p f
          wsc              = return $ weakSafeCompP p
          pext              = return $ prodExtP p
indexed :: [a] -> [(a, Int)]
indexed = flip zip [1..]
