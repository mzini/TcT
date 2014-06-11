{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}

{- | 
Module      :  Tct.Method.Mpo
Copyright   :  (c) Martin Avanzini <martin.avanzini@uibk.ac.at>, 
               Georg Moser <georg.moser@uibk.ac.at>, 
               Andreas Schnabl <andreas.schnabl@uibk.ac.at>
License     :  LGPL (see COPYING)

Maintainer  :  Martin Avanzini <martin.avanzini@uibk.ac.at>
Stability   :  unstable
Portability :  unportable      

This module defines the MPO processors.
-}


module Tct.Method.Mpo 
       (
         MpoOrder (..)      
       , mpo      
       , ppo         
       , Mpo
       , mpoProcessor
       )
       where

import Control.Monad (liftM)
import Data.Maybe (isJust)
import Prelude hiding ((&&),(||),not)
import Data.Typeable (Typeable)
import qualified Data.Set as Set
import qualified Data.IntSet as IntSet
import Text.PrettyPrint.HughesPJ hiding (empty)
import qualified Text.PrettyPrint.HughesPJ as PP

import Termlib.FunctionSymbol (Symbol)
import Termlib.Problem (Problem)
import Termlib.Rule (lhs, rhs, Rule)
import Termlib.Term
import Termlib.Trs (Trs, rules)
import Termlib.Trs.PrettyPrint (pprintTrs)
import Termlib.Utils (PrettyPrintable(..),($++$), block, paragraph)
import qualified Termlib.ArgumentFiltering as AF
import qualified Termlib.Precedence as Prec
import qualified Termlib.Problem as Prob
import Termlib.Problem (Problem (..))
import qualified Termlib.Trs as Trs

import Qlogic.Boolean
import Qlogic.PropositionalFormula
import Qlogic.MemoizedFormula
import Qlogic.MiniSat
import Qlogic.SatSolver ((:&:) (..), addFormula)
import qualified Qlogic.SatSolver as S

import Tct.Certificate (primrec, certified, unknown)
import Tct.Processor.Standard
import qualified Tct.Processor as P
import Tct.Processor.Orderings
-- import Tct.Processor.Args
import qualified Tct.Processor.Args as A
import Tct.Processor.Args.Instances ()
import Tct.Processor (ComplexityProof(..), Answer (..))
import qualified Tct.Encoding.Precedence as PrecEnc
import qualified Tct.Encoding.UsableRules as UREnc
import qualified Tct.Encoding.ArgumentFiltering as AFEnc
import Tct.Encoding.Relative hiding (trs)

data Mpo = Mpo deriving (Show)


mpoProcessor :: StdProcessor Mpo
mpoProcessor = StdProcessor Mpo

-- | This processor implements multiset path orders.
mpo :: P.InstanceOf (StdProcessor Mpo)
mpo = mpoProcessor `withArgs` False

-- | This processor implements product path orders.
ppo :: P.InstanceOf (StdProcessor Mpo)
ppo = mpoProcessor `withArgs` True


-- | Proof Object generated by Mpo
data MpoOrder = MpoOrder 
                { 
                  mpoPrecedence :: Prec.Precedence -- ^ Precedence underlying the order.
                , mpoArgumentFiltering :: Maybe AF.ArgumentFiltering  -- ^ Argument filtering underlying the order.
                , mpoUsableSymbols     :: [Symbol] -- ^ Defined symbols of usable rules.                  
                , mpoInputProblem :: Problem -- ^ The input Problem.
                , mpoIsPPO :: Bool
                } 
              deriving Show

instance ComplexityProof MpoOrder where
  pprintProof order _ = paragraph ("The input was oriented with the instance of" 
                                   ++ "'" ++ nm ++ "' as induced by the precedence")
                        $++$ (pparam prec <+> text ".")
                        $+$ (case maf of 
                               Nothing -> PP.empty
                               Just af -> text "" 
                                         $+$ text "Further, following argument filtering is employed:"
                                         $++$ pparam af
                                         $++$ paragraph ( "Applying the argument filtering on the input problem results in "
                                                          ++ "the following rules (here only usable rules modulo the argument filtering are shown).")   
                                         $++$ pparam ppProblem
                            )
  
      where pparam :: PrettyPrintable p => p -> Doc 
            pparam   = nest 1 . pprint
            nm | mpoIsPPO order  = "product path order" 
               | otherwise       = "multiset path order"
            prec            = mpoPrecedence order
            ppProblem = ppTrs     "Strict DPs"   strictDPs
                        $+$ ppTrs "Weak DPs  "   weakDPs
                        $+$ ppTrs "Strict Trs"   (restrictUsables . strictTrs)
                        $+$ ppTrs "Weak Trs  "   (restrictUsables . weakTrs)

            ppTrs n sel = block n $ pprintTrs (\ rl -> fsep [pp (lhs rl), text "->", pp (rhs rl)]) (rules $ sel prob)
              where pp (Var x) = pprint (x,vars)
                    pp (Fun f ts) = 
                      case AF.filtering f af of 
                        AF.Projection i -> pp (ts!!(i-1))
                        AF.Filtering is -> pprint (f,sig) <> parens ppa
                          where ppa = sep $ punctuate (text ",") [pp ti | (i,ti) <- zip [1..] ts
                                                                        , i `IntSet.member` is]
                    af = maybe (AF.empty sig) id maf
            
            restrictUsables trs | isJust maf = Trs.filterRules 
                                               (\ rl -> case root (lhs rl) of 
                                                   Right f -> f `elem` us
                                                   Left _  -> True) trs
                                | otherwise  = trs

            prob = mpoInputProblem order
            sig            = Prob.signature prob
            vars           = Prob.variables prob
            us             = mpoUsableSymbols order
            maf            = mpoArgumentFiltering order

  answer _ = CertAnswer $ certified (unknown, primrec)
  

instance Processor Mpo where
   name _ = "mpo"
   instanceName inst | prod = "product path order"
                     | otherwise = "multiset path order"
     where prod = processorArgs inst
   description _ = ["This processor implements 'multiset path orders' as found in the literature."]
   type ArgumentsOf Mpo = A.Arg Bool
   type ProofOf Mpo     = OrientationProof MpoOrder
   arguments _ =
     A.opt { A.name = "product"
           , A.description = "Product: If enabled, use product extension instead of multiset extension."
           , A.defaultValue = False }


   solve inst prob = orientProblem prod prob 
     where prod = processorArgs inst

data Predicates l = Predicates { collapsingP :: Symbol -> PropFormula l
                               , inFilterP :: Symbol -> Int -> PropFormula l
                               , precGtP :: Symbol -> Symbol -> PropFormula l
                               , precEqP :: Symbol -> Symbol -> PropFormula l}

data MpoArg = Gt Term Term
            | Eq Term Term
              deriving (Eq, Ord, Show)

orientProblem :: P.SolverM m => Bool -> Problem -> m (OrientationProof MpoOrder)
orientProblem prod prob = maybe Incompatible Order `liftM` slv 
    where allowAF   = (isDP && Trs.isEmpty (Prob.strictTrs prob))
          isDP      = Prob.isDPProblem prob
          
          stricts  = Prob.strictComponents prob
          weaks    = Prob.weakComponents prob
          allrules = Prob.allComponents prob
          fs = Set.toList $ Trs.functionSymbols allrules
          sig      = Prob.signature prob

          slv | isDP      = solveDP 
              | otherwise = solveDirect
          
          solveDP = solveConstraint form initial mkOrd
              where mkOrd (us :&: prec :&: af) = 
                      MpoOrder { mpoPrecedence        = prec
                               , mpoArgumentFiltering = Just af 
                               , mpoInputProblem      = prob 
                               , mpoUsableSymbols     = us 
                               , mpoIsPPO             = prod}
                    initial = UREnc.initialUsables prob
                              :&: PrecEnc.initial sig 
                              :&: AFEnc.initial sig

          solveDirect = solveConstraint form initial mkOrd
              where mkOrd prec = 
                      MpoOrder { mpoPrecedence        = prec
                               , mpoArgumentFiltering = Nothing
                               , mpoInputProblem      = prob 
                               , mpoUsableSymbols     = Set.toList $ Trs.definedSymbols $ Prob.trsComponents prob 
                               , mpoIsPPO             = prod}
                    initial = PrecEnc.initial sig

          solveConstraint :: (S.Decoder e a) => P.SolverM m => MemoFormula MpoArg MiniSatSolver MiniSatLiteral -> e -> (e -> b) -> m (Maybe b)
          solveConstraint constraint initial makeResult = 
              do r <- P.minisatValue (toFormula constraint >>= addFormula) initial
                 return $ makeResult `liftM` r

          form = bigAnd [not (usable r) || propAtom (strictlyOriented r) | r <- rules stricts]
                 && bigAnd [not (usable r) || propAtom (weaklyOriented r)   | r <- rules weaks]
                 && validPrecedence
                 && (fm allowAF --> validArgumentFiltering)
                 && validUsableRules
                 && orderingConstraints allowAF prod stricts weaks

          usable = return . UREnc.usable prob
            
          
          validArgumentFiltering = return $ AFEnc.validSafeArgumentFiltering fs sig
          validPrecedence        = liftSat $ PrecEnc.validPrecedenceM fs
          validUsableRules = liftSat $ toFormula $ UREnc.validUsableRulesEncoding prob isUnfiltered                    
            where isUnfiltered f i | allowAF   = AFEnc.isInFilter f i
                                   | otherwise = top
                                                 

orderingConstraints :: (S.Solver s l, Eq l, Show l, Ord l) => Bool -> Bool -> Trs -> Trs -> MemoFormula MpoArg s l
orderingConstraints allowAF useProd strict weak = 
    strict `orientStrictBy` mpoSt && weak `orientWeakBy` mpoEq
      where orientBy ob trs ord = bigAnd [propAtom (ob r) --> lhs r `ord` rhs r | r <- rules trs]
            orientStrictBy = orientBy strictlyOriented 
            orientWeakBy = orientBy weaklyOriented
            mpoSt s t       = orient useProd preds (Gt s t)
            mpoEq s t       = orient useProd preds (Eq s t) || mpoSt s t
            preds           = Predicates { collapsingP = if allowAF then AFEnc.isCollapsing else const bot
                                         , inFilterP   = if allowAF then AFEnc.isInFilter else const . const top
                                         , precGtP     = PrecEnc.precGt
                                         , precEqP     = PrecEnc.precEq} 


newtype DeltaAtom   = Delta   (Int, Int, (Term, Term)) deriving (Eq, Ord, Typeable, Show)
newtype EpsilonAtom = Epsilon (Int, (Term, Term))      deriving (Eq, Ord, Typeable, Show)
newtype GammaAtom   = Gamma   (Int, Int, (Term, Term)) deriving (Eq, Ord, Typeable, Show)

instance PropAtom DeltaAtom
instance PropAtom EpsilonAtom
instance PropAtom GammaAtom


orient :: (S.Solver s l, Eq l, Show l) => Bool -> Predicates l -> (MpoArg -> MemoFormula MpoArg s l)
orient useProd p = 
  memoized $ \ a -> 
  case a of 
    Gt (Var _)      _ -> bot
    Gt s@(Fun f ss) t -> case1 || case2 || case3 t
      where iss = indexed ss 
            case1 = not (isCollapsing f) && exist iss (\ (s_i, i) -> inFilter f i && (s_i `equiv` t))
            case2 = exist iss (\ (s_i, i) -> inFilter f i && s_i `gmpo` t)
            case3 (Var _)    = bot
            case3 (Fun g ts) = not (isCollapsing f) 
                               && (((not (isCollapsing g) --> f `pGt` g) && bigAnd [inFilter g j --> s `gmpo` t_j | (t_j,j) <- its])
                               || (not (isCollapsing g) && f `pEq` g && mulGt))
                           where mulGt = (forall js (\ j -> inFilter g j --> exist is (\i -> gamma i j)))
                                         && (forall is $ \ i -> (inFilter f i || forall js (\ j -> not (gamma i j))))
                                         && (forall is $ \ i -> ((epsilon i || fm useProd)--> exactlyOne [gamma i j | j <- js]))
                                         && exist is (\ i -> not (epsilon i) && inFilter f i)
                                         && bigAnd [gamma i j --> inFilter f i && ite (epsilon i) (s_i `equiv` t_j) (s_i `gmpo` t_j)
                                               | (s_i, i) <- iss, (t_j, j) <- its]
                                 its = indexed ts
                                 is  = [i | (_, i) <- iss]
                                 js  = [j | (_, j) <- its]
                                 gamma i j   = return $ propAtom $ Gamma (i, j, (s, t))
                                 epsilon i   = return $ propAtom $ Epsilon (i, (s, t))

    Eq (Var v1)     (Var v2)     -> fm $ v1 == v2
    Eq v@(Var _)    t@(Fun _ _) -> t `equiv` v
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
                                                                           , s_i `equiv` t_j])
                       encodeDelta             = ( forall is $ \ i -> inFilter f i --> exactlyOne [delta i j | j <- js])
                                                 && ( forall js $ \ j -> inFilter g j --> exactlyOne [delta i j | i <- is])

    where s `gmpo` t = orient useProd p (Gt s t)
          s `equiv` t      = orient useProd p (Eq s t)
          pGt f g          = return $ precGtP p f g
          pEq f g          = return $ precEqP p f g
          inFilter f i     = return $ inFilterP p f i
          isCollapsing f   = return $ collapsingP p f

indexed :: [a] -> [(a, Int)]
indexed = flip zip [1..]
