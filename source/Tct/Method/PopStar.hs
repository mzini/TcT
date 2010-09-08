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

module Tct.Method.PopStar where

import Control.Monad (liftM2, liftM)
import Data.Set (Set, (\\))
import qualified Data.Set as Set
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

import Termlib.FunctionSymbol (Symbol, Signature)
import Termlib.Problem (Problem)
import Termlib.Problem (StartTerms(..), Strategy(..), Relation(..))
import Termlib.Rule (lhs, rhs, Rule)
import Termlib.Signature (runSignature)
import Termlib.Term
import Termlib.Trs (Trs, rules)
import Termlib.Utils (PrettyPrintable(..), ($++$))
import qualified Termlib.ArgumentFiltering as AF
import qualified Termlib.Precedence as Prec
import qualified Termlib.Problem as Prob
import qualified Termlib.Trs as Trs

import Tct.Certificate (poly, expo, certified, uncertified, unknown)
import Tct.Proof
import qualified Tct.Processor.Standard as S
import qualified Tct.Processor as P
import Tct.Processor.Orderings
import Tct.Processor.Args
import Tct.Processor.Args.Instances ()
import qualified Tct.Processor.Args as A
import Tct.Encoding.Relative hiding (trs)
import qualified Tct.Encoding.ArgumentFiltering as AFEnc
import qualified Tct.Encoding.Precedence as PrecEnc
-- import qualified Tct.Encoding.Relative as Rel
import qualified Tct.Encoding.SafeMapping as SMEnc

data PopStarOrder = PopOrder { popSafeMapping       :: SMEnc.SafeMapping
                             , popPrecedence        :: Prec.Precedence
                             , popArgumentFiltering :: Maybe AF.ArgumentFiltering
                             , popInputProblem      :: Problem
                             , popMultRecAllowed    :: Bool
                             , popPsAllowed         :: Bool}
                    deriving Show


instance PrettyPrintable PopStarOrder where
  pprint order = (text "The input was oriented with the instance of" <+> text ordname <+> text "as induced by the precedence")
                 $++$ pparam (popPrecedence order)
                 $++$ text "and safe mapping"
                 $++$ pparam (popSafeMapping order) <+> text "."
                 $+$ (case popArgumentFiltering order of 
                               Nothing -> PP.empty
                               Just af -> text "Further, following argument filtering is employed:"
                                         $++$ pparam af)
                 $++$ text "For your convenience, here is the input in predicative notation:"
                 $++$ nest 1 (ppstrict $+$ ppweak)
      where pparam :: PrettyPrintable p => p -> Doc 
            pparam = nest 1 . pprint
            ordname | popMultRecAllowed order = "LMPO"
                    | otherwise               = "POP*"
            ppstrict       = text "Rules:" $$ pparam (strict, sig, vars, sm)
            ppweak | length (Trs.rules weak) == 0 = PP.empty 
                   | otherwise                    = text "Weak Rules:" $$ pparam (weak, sig, vars, sm)

            (strict, weak, sig) = case (Prob.relation $ prob, popArgumentFiltering order) of 
                                    (Standard trs, _) -> (trs, Trs.empty, Prob.signature prob)
                                    (Relative s w, _) -> (s, w, Prob.signature prob)
                                    (DP s w, Just af) -> (strict', weak', sig')
                                            where ((strict',weak'),sig') = runSignature (liftM2 (,) (AF.apply s af) (AF.apply w af)) (Prob.signature prob)
                                    (DP s w      , _) -> (s, w, Prob.signature prob)

            vars           = Prob.variables prob
            prob           = popInputProblem order
            sm             = popSafeMapping order

instance Answerable PopStarOrder where
    answer order | popMultRecAllowed order && popPsAllowed order = CertAnswer $ uncertified
                 | popMultRecAllowed order                       = CertAnswer $ certified (unknown, expo Nothing)
                 | otherwise                                     = CertAnswer $ certified (unknown, poly Nothing)

instance ComplexityProof PopStarOrder

data PopStar = PopStar {isLmpo :: Bool} deriving (Typeable, Show)

instance S.StdProcessor PopStar where
    name p | isLmpo p  = "lmpo"
           | otherwise = "pop*"

    description p | isLmpo p  = [ unlines [ "This processor implements orientation of the input problem using 'light multiset path orders',"
                                          , "a technique applicable for innermost runtime-complexity analysis."
                                          , "Light multiset path orders are a miniaturisation of 'multiset path orders',"
                                          , "restricted so that compatibility assesses polytime computability of the functions defined, "
                                          , "cf. http://www.loria.fr/~marionjy/Papers/icc99.ps ."
                                          , "Further, it induces exponentially bounded innermost runtime-complexity."]
                                ]
                  | otherwise = [ unlines [ "This processor implements orientation of the input problem using 'polynomial path orders',"
                                          , "a technique applicable for innermost runtime-complexity analysis."
                                          , "Polynomial path orders are a miniaturisation of 'multiset path orders',"
                                          , "restricted so that compatibility assesses a polynomial bound on the innermost runtime-complexity, "
                                          , "cf. http://cl-informatik.uibk.ac.at/~zini/publications/FLOPS08.pdf ."]
                                , unlines [ "The implementation for the WDP-setting follows closely"
                                          , "http://cl-informatik.uibk.ac.at/~zini/publications/RTA09.pdf ,"
                                          , "where addionally argument filterings are employed." ]
                                ]

    type S.ArgumentsOf PopStar = Arg Bool

    instanceName inst = S.name $ S.processor inst

    arguments _ = opt { A.name = "ps"
                      , A.description = unlines [ "If enabled then the scheme of parameter substitution is admitted,"
                                                 , "cf. http://cl-informatik.uibk.ac.at/~zini/publications/WST09.pdf how this is done for polynomial path orders." ]
                      , A.defaultValue = True }

    type S.ProofOf PopStar = OrientationProof PopStarOrder
    solve inst prob = case (Prob.startTerms prob, Prob.strategy prob) of 
                     ((BasicTerms _ cs), Innermost) -> orientProblem (isLmpo $ S.processor inst) (S.processorArgs inst) cs prob
                     _                              -> return Incompatible




popstarProcessor :: S.Processor PopStar
popstarProcessor = S.Processor (PopStar False)

lmpoProcessor :: S.Processor PopStar
lmpoProcessor = S.Processor (PopStar True)


quasiConstructorsFor :: Set Symbol -> Trs -> Trs -> Set Symbol
quasiConstructorsFor constructors strict weak = constructors
                                                `Set.union` (quasiConstructors strict)
                                                `Set.union` (quasiConstructors weak)
    where quasiConstructors rs = Set.unions [qd (lhs r) | r <- rules rs ]
          qd (Fun _ ts) = Set.unions [ functionSymbols t | t <- ts] 
          qd _          = error "Method.PopStar: non-trs given"



data Predicates l = Predicates {
      definedP :: Symbol -> PropFormula l
    , collapsingP :: Symbol -> PropFormula l
    , inFilterP :: Symbol -> Int -> PropFormula l
    , safeP :: Symbol -> Int -> PropFormula l
    , precGtP :: Symbol -> Symbol -> PropFormula l
    , precEqP :: Symbol -> Symbol -> PropFormula l
    , allowMulRecP :: PropFormula l
    , allowPsP :: PropFormula l
  }


data PopArg = Gt Term Term
            | Gsq Term Term
            | Eq Term Term
              deriving (Eq, Ord, Show)


orientProblem :: Bool -> Bool -> Set Symbol -> Problem -> P.SolverM (OrientationProof PopStarOrder)
orientProblem lmpo ps cs prob = maybe Incompatible Order `liftM` slv (Prob.relation prob)
                                    
    where slv (Standard trs) = solveConstraint form initial mkOrd
              where mkOrd (sm :&: prec) = PopOrder sm prec Nothing prob lmpo ps
                    form                = directConstraint lmpo ps quasiConstrs trs Trs.empty sig 
                                          && bigAnd [atom $ strictlyOriented r | r <- rules trs]
                    initial             = SMEnc.empty sig quasiConstrs :&: Prec.empty sig
                    quasiConstrs        = quasiConstructorsFor cs trs Trs.empty
          slv (DP strict weak) = solveConstraint form initial mkOrd
              where mkOrd (sm :&: prec :&: af) = PopOrder sm prec (Just af) prob False ps
                    form                = dpConstraint ps quasiConstrs strict weak sig 
                                          && bigAnd [atom $ strictlyOriented r | r <- rules strict]
                                          && bigAnd [atom $ weaklyOriented r | r <- rules weak]
                    initial             = SMEnc.empty sig quasiConstrs :&: Prec.empty sig :&: AFEnc.initial sig
                    quasiConstrs        = quasiConstructorsFor cs strict weak

          slv (Relative strict weak) = solveConstraint form initial mkOrd
              where mkOrd (sm :&: prec) = PopOrder sm prec Nothing prob lmpo ps
                    form                = directConstraint lmpo ps quasiConstrs strict weak sig 
                                          && bigAnd [atom $ strictlyOriented r | r <- rules $ strict]
                                          && bigAnd [atom $ weaklyOriented r | r <- rules $ weak]
                    initial             = SMEnc.empty sig quasiConstrs :&: Prec.empty sig
                    quasiConstrs        = quasiConstructorsFor cs strict weak 

          sig  = Prob.signature prob
 
solveConstraint:: (S.Decoder e a) => MemoFormula PopArg MiniSatSolver MiniSatLiteral -> e -> (e -> b) -> P.SolverM (Maybe b)
solveConstraint constraint initial makeResult = 
    do r <- P.minisatValue (toFormula constraint >>= addFormula) initial
       return $ makeResult `liftM` r


directConstraint :: (S.Solver s l, Eq l, Show l) => Bool -> Bool -> Set Symbol -> Trs -> Trs -> Signature -> MemoFormula PopArg s l
directConstraint allowMR allowPS quasiConstrs strict weak _ = fm maybeOrientable && 
                                                              strict `orientStrictBy` pop 
                                                              && weak `orientWeakBy` popEq
                                                              && validPrecedence

  where maybeOrientable     = allowMR || (all maybeOrientableRule $ rules both)
            where maybeOrientableRule r = case rtl of 
                                            Left  _   -> False 
                                            Right sym -> sym `Set.member` quasiDefinedSymbols --> cardinality rtl (rhs r) <= 1
                      where rtl = root (lhs r)

        both                = strict `Trs.union` weak
        quasiDefinedSymbols = Trs.definedSymbols both \\ quasiConstrs
        pop s t             = orient preds (Gt s t)
        popEq s t           = orient preds (Eq s t) || orient preds (Gt s t)
        preds               = Predicates {
                                definedP    = defP
                              , collapsingP = const bot
                              , inFilterP   = const . const top
                              , safeP       = \ f i -> not (defP f) || SMEnc.isSafeP f i
                              , precGtP     = \ f g -> defP f && (not (defP g) || f `PrecEnc.precGt` g)
                              , precEqP     = \ f g -> (not (defP f) && not (defP g)) || (defP f && defP g && f `PrecEnc.precEq` g)
                              , allowMulRecP = fm allowMR
                              , allowPsP     = fm allowPS
                              } where defP f = fm $ f `Set.member` quasiDefinedSymbols
        validPrecedence     = liftSat $ PrecEnc.validPrecedenceM (Set.toList quasiDefinedSymbols)

dpConstraint :: (S.Solver s l, Eq l, Show l, Ord l) => Bool -> Set Symbol -> Trs -> Trs -> Signature -> MemoFormula PopArg s l
dpConstraint allowPS quasiConstrs strict weak sig = strict `orientStrictBy` pop 
                                                    && weak `orientWeakBy` popEq
                                                    && validPrecedence 
                                                    && validArgumentFiltering
    where both                = strict `Trs.union` weak
          allSymbols          = Trs.functionSymbols both
          quasiDefinedSymbols = Trs.definedSymbols both \\ quasiConstrs
          pop s t             = orient preds (Gt s t)
          popEq s t           = orient preds (Eq s t) || pop s t
          preds               = Predicates {
                                  definedP    = defP
                                , collapsingP = AFEnc.isCollapsing
                                , inFilterP   = AFEnc.isInFilter
                                , safeP       = \ f i  -> not (defP f) || SMEnc.isSafeP f i
                                , precGtP     =  \ f g -> fm (f /= g) && defP f && (not (defP g) || f `PrecEnc.precGt` g)
                                , precEqP     = \ f g  -> (fm (f == g) 
                                                          || not (defP f) && not (defP g)
                                                          || defP f && defP g && f `PrecEnc.precEq` g)
                                , allowMulRecP = bot
                                , allowPsP     = fm allowPS
                            } where defP f = fm $ f `Set.member` quasiDefinedSymbols
          validArgumentFiltering = return $ AFEnc.validSafeArgumentFiltering (Set.toList allSymbols) sig
          validPrecedence        = liftSat $ PrecEnc.validPrecedenceM (Set.toList quasiDefinedSymbols)


newtype AlphaAtom   = Alpha   (Int, (Term, Term))      deriving (Eq, Ord, Typeable, Show)
newtype DeltaAtom   = Delta   (Int, Int, (Term, Term)) deriving (Eq, Ord, Typeable, Show)
newtype EpsilonAtom = Epsilon (Int, (Term, Term))      deriving (Eq, Ord, Typeable, Show)
newtype GammaAtom   = Gamma   (Int, Int, (Term, Term)) deriving (Eq, Ord, Typeable, Show)

instance PropAtom AlphaAtom
instance PropAtom DeltaAtom
instance PropAtom EpsilonAtom
instance PropAtom GammaAtom


orientBy :: (S.Solver s l, Eq l) => (Rule -> Orientation) -> Trs ->  (Term -> Term -> MemoFormula PopArg s l) -> MemoFormula PopArg s l
orientBy ob trs ord = bigAnd [atom (ob r) --> lhs r `ord` rhs r | r <- rules trs]

orientStrictBy :: (S.Solver s l, Eq l) => Trs ->  (Term -> Term -> MemoFormula PopArg s l) -> MemoFormula PopArg s l
orientStrictBy = orientBy strictlyOriented

orientWeakBy :: (S.Solver s l, Eq l) => Trs ->  (Term -> Term -> MemoFormula PopArg s l) -> MemoFormula PopArg s l
orientWeakBy = orientBy weaklyOriented


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
                                              && bigAnd [inFilter g j 
                                                    --> bigAnd [isCollapsing g 
                                                         || (isDefined f 
                                                             && (not (f `pGt` g) || isSafe g j || s `gsq` t_j)
                                                             && bigOr [ isNormal g j
                                                                  , precRestrictedP f t_j
                                                                  , f `pGt` g && alpha j])
                                                        , s `gpop` t_j || not (isCollapsing g) && isNormal g j]
                                                        | (t_j, j) <- its ]
                                              && (isCollapsing g 
                                                  || (f `pGt` g && (mulRecForbidden --> atmostOne [alpha j | (_,j) <- its]))
                                                  || (f `pEq` g && isDefined f && mulGt))
                                     where mulGt = encodeCover
                                                   && bigAnd [gamma i j --> bigAnd [ inFilter f i
                                                                       , ite paramSubst 
                                                                                 (isNormal f i) 
                                                                                 (isSafe f i <-> isSafe g j)
                                                                       , ite (epsilon i) (s_i `equiv` t_j) (s_i `gpop` t_j)]
                                                         | (s_i, i) <- iss, (t_j, j) <- its]
                                                   && bigOr [not (epsilon i) && isNormal f i && inFilter f i | i <- is]
                                           encodeCover = (forall js $ \ j ->  
                                                              inFilter g j && (paramSubst --> isNormal g j) --> bigOr [gamma i j | i <- is])
                                                         && (forall is $ \ i -> 
                                                             (paramSubst --> (inFilter f i && isNormal f i || bigAnd [not (gamma i j) | j <- js]))
                                                             && (epsilon i --> exactlyOne [gamma i j | j <- js]))
                                           its = indexed ts
                                           is  = [i | (_, i) <- iss]
                                           js  = [j | (_, j) <- its]
                                           alpha j     = return $ propAtom $ Alpha (j, (s, t))
                                           gamma i j   = return $ propAtom $ Gamma (i, j, (s, t))
                                           epsilon i   = return $ propAtom $ Epsilon (i, (s, t))
                                           isNormal f' i = not (isSafe f' i)
                                           mulRecForbidden = return $ not (allowMulRecP p)
                                           paramSubst = return $ allowPsP p
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
                       case3 = case t of 
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


indexed :: [a] -> [(a, Int)]
indexed = flip zip [1..]
