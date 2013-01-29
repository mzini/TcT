{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}

{- | 
Module      :  Tct.Method.PopStar
Copyright   :  (c) Martin Avanzini <martin.avanzini@uibk.ac.at>, 
               Georg Moser <georg.moser@uibk.ac.at>, 
               Andreas Schnabl <andreas.schnabl@uibk.ac.at>
License     :  LGPL (see COPYING)

Maintainer  :  Martin Avanzini <martin.avanzini@uibk.ac.at>
Stability   :  unstable
Portability :  unportable      

This module defines the POP* and LMPO processors.
-}

module Tct.Method.PopStar 
    ( 
      -- * Proof Object
      PopStarOrder (..)      
      
      -- * Instance Constructors
    , popstar
    , popstarPS
    , popstarSmall
    , popstarSmallPS
    , lmpo
      
      -- * Processors
    , PopStar      
      -- | The processor object.
    , popstarProcessor
      -- | Popstar processor.
    , ppopstarProcessor
      -- | Popstar processor with product extension. Set argument @wsc@
      -- to get small polynomial path orders
    , lmpoProcessor
      -- | Lightweight multiset path order processor.      
    )
where

import Control.Monad (liftM)
import Data.Set (Set, (\\))
import Data.Maybe (isJust, catMaybes, fromMaybe)
import Data.List (partition)
import qualified Data.Set as Set
import qualified Data.IntSet as IntSet
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

import Termlib.FunctionSymbol (Symbol, isMarked, isCompound, arity)
import Termlib.Problem (StartTerms(..), Strategy(..), Problem(..))
import Termlib.Rule (lhs, rhs, Rule)
-- import Termlib.Signature (runSignature)
import Termlib.Term
import Termlib.Trs (Trs, rules)
import Termlib.Utils (PrettyPrintable(..), ($++$), paragraph)
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
import Tct.Processor.Args.Instances (nat, Nat(..))
import qualified Tct.Processor.Args as A
import Tct.Encoding.Relative hiding (trs)
import qualified Tct.Encoding.ArgumentFiltering as AFEnc
import qualified Tct.Encoding.UsableRules as UREnc
import qualified Tct.Encoding.Precedence as PrecEnc
-- import qualified Tct.Encoding.Relative as Rel
import qualified Tct.Encoding.SafeMapping as SMEnc
import Tct.Utils.PPrint (columns, Align (..), indent)


allCompoundsMonadic :: Problem -> Bool
allCompoundsMonadic prob = all ifCompoundMonadic [ root (rhs r) | r <- Trs.rules $ Prob.dpComponents prob]
  where sig = Prob.signature prob
        ifCompoundMonadic (Left _) = True
        ifCompoundMonadic (Right f) 
          | isCompound sig f = arity sig f <= 1
          | otherwise = True

--------------------------------------------------------------------------------
--- proof object



data OrdType = POP | SPOP | LMPO deriving (Typeable, Show, Eq)

data PopStar = PopStar { kind :: OrdType } deriving (Typeable, Show)


data PopStarOrder = PopOrder { popSafeMapping       :: SMEnc.SafeMapping -- ^ The safe mapping.
                             , popPrecedence        :: Prec.Precedence -- ^ The precedence.
                             , popRecursives        :: PrecEnc.RecursiveSymbols -- ^ Recursive symbols.
                             , popArgumentFiltering :: Maybe AF.ArgumentFiltering -- ^ Employed argument filtering.
                             , popInputProblem      :: Problem -- ^ The input problem.
                             , popInstance          :: S.TheProcessor PopStar -- ^ The specific instance employed.
                             , popUsableSymbols     :: [Symbol] -- ^ Defined symbols of usable rules.
                             , popStrictlyOriented  :: Trs -- ^ The rules that were effectively strictly oriented.
                             }

instance ComplexityProof PopStarOrder where
  pprintProof order _ = paragraph ("The input was oriented with the instance of '" 
                                   ++ S.instanceName inst ++ "' as induced by the safe mapping")
                        $++$ pparam (popSafeMapping order)
                        $++$ text "and precedence"
                        $++$ (pparam prec <+> text ".")
                        $++$ paragraph "Following symbols are considered recursive:"
                        $++$ pparam (braces $ fsep $ punctuate (text ",")  [pprint (f,sig) | f <- Set.toList rs])
                        $++$ paragraph( "The recursion depth is " ++ show recdepth ++ ".")
                        $+$ (case maf of 
                               Nothing -> PP.empty
                               Just af -> text "" 
                                         $+$ paragraph "Further, following argument filtering is employed:"
                                         $++$ pparam af
                                         $++$ paragraph "Usable defined function symbols are a subset of:"
                                         $++$ pparam (braces $ fsep $ punctuate (text ",")  [pprint (f,sig) | f <- us]))
                        $++$ paragraph ("For your convenience, here are the satisfied ordering constraints:")
                        $++$ indent ppOrient
      where pparam :: PrettyPrintable p => p -> Doc 
            pparam   = nest 1 . pprint
            recdepth = maximum (0 : Map.elems (Prec.recursionDepth rs prec))
            (PrecEnc.RS rs) = popRecursives order
            prec            = popPrecedence order
            inst = popInstance order
            ppOrient =   columns [ (AlignRight, as)
                                 , (AlignLeft, bs)
                                 , (AlignLeft, cs)]
              where (as,bs,cs) = unzip3 $ concatMap ppOrientRl trs
                    trs = Trs.rules (Prob.dpComponents prob) ++ Trs.rules (restrictUsables (Prob.trsComponents prob))
                    ppOrientRl rl = 
                      case maf of 
                        Just _ ->  [ (ppPi (lhs rl), text " = ", pp (lhs rl))
                                   , (text ""     , arr rl  , pp (rhs rl))
                                   , (text ""     , text " = ", ppPi (rhs rl)) 
                                   , nl]
                        Nothing -> [ (pp (lhs rl)  , arr rl  , pp (rhs rl)) 
                                  , nl ]
                    nl = (text " ", text " ", text " ")
                    arr rl | Trs.member sr rl = text " > "
                           | otherwise        = text " >= "
                    ppPi t = text "pi" <> parens (pprint (t,sig,vars))                            
                    pp (Var x) = pprint (x,vars)
                    pp (Fun f ts) = 
                      case AF.filtering f af of 
                        AF.Projection i -> pp (ts!!(i-1))
                        AF.Filtering is -> pprint (f,sig) <> parens ( ppargs )
                          where (safes,normals) = IntSet.partition (SMEnc.isSafe sm f) is
                                ppargs | IntSet.null is = PP.empty
                                       | otherwise      = ppa normals <> sc <> ppa safes
                                ppa poss        = sep $ punctuate (text ", ") [pp ti | (i,ti) <- zip [1..] ts
                                                                                     , i `IntSet.member` poss]
                                sc | IntSet.null safes = text ";"
                                   | otherwise         = text "; "
                    af = maybe (AF.empty sig) id maf
            prob           = popInputProblem order
            sig            = Prob.signature prob
            vars           = Prob.variables prob
            sm             = popSafeMapping order
            us             = popUsableSymbols order
            maf            = popArgumentFiltering order
            sr             = popStrictlyOriented order
            restrictUsables trs | isJust maf = Trs.filterRules 
                                               (\ rl -> case root (lhs rl) of 
                                                   Right f -> f `elem` us
                                                   Left _  -> True) trs
                                | otherwise  = trs
                             

  answer order = case kind $ S.processor inst of 
                   LMPO    -> CertAnswer $ certified (unknown, expo Nothing)
                   POP     -> CertAnswer $ certified (unknown, poly Nothing)
                   SPOP | wsc       -> CertAnswer $ certified (unknown, poly $ Just ub) 
                        | otherwise -> CertAnswer $ certified (unknown, poly Nothing)
      where inst       = popInstance order
            _ :+: wsc :+: _ = S.processorArgs inst
            ub              = modifyUB $ maximum (0 : Map.elems (Prec.recursionDepth rs prec))
            (PrecEnc.RS rs) = popRecursives order
            prec            = popPrecedence order
            modifyUB d = 
              case popArgumentFiltering order of --TODO verify DP setting
                Just af | not $ hasProjection af -> d
                        | allCompoundsMonadic prob -> max 1 d
                        | otherwise -> max 1 (2 * d)
                Nothing -> d
            sig = Prob.signature prob
            prob = popInputProblem order
            hasProjection af = AF.fold (\ sym filtering -> (||) (f sym filtering)) af False
              where f sym (AF.Projection _) | isMarked sig sym = True
                                            | otherwise        = False
                    f _ _                                      = False

--------------------------------------------------------------------------------
--- processor 

argPS :: Arg Bool
argPS = 
  opt { A.name = "ps"
      , A.description = "Parameter substitution: If enabled, parameter substitution is allowed, strengthening the order."
      , A.defaultValue = False }
  
argWSC :: Arg Bool
argWSC = 
  opt { A.name = "wsc"
      , A.description = "Weak Safe Composition: If enabled then composition is restricted to weak safe composition."
      , A.defaultValue = False }
         
argDeg :: Arg (Maybe Nat)
argDeg = 
  opt { A.name = "deg"
      , A.description = unwords [ "Deg: If set and applicable, polynomially bounded runtime complexity with given degree is proven." 
                                , "This flag only works in combination with product extension and weak safe composition, "
                                , "cf. 'popstarSmall'."]
      , A.defaultValue = Nothing }

instance S.Processor PopStar where
    name p = case kind p of 
               LMPO -> "lmpo"
               POP  -> "popstar"
               SPOP -> "popstarSmall"

    description p = 
      case kind p of 
        LMPO -> [ unwords [ "This processor implements orientation of the input problem using 'light multiset path orders',"
                         , "a technique applicable for innermost runtime-complexity analysis."
                         , "Light multiset path orders are a miniaturisation of 'multiset path orders',"
                         , "restricted so that compatibility assesses polytime computability of the functions defined."
                         , "Further, it induces exponentially bounded innermost runtime-complexity."]]
        POP   -> [ unwords [ "This processor implements orientation of the input problem using 'polynomial path orders',"
                          , "a technique applicable for innermost runtime-complexity analysis."
                          , "Polynomial path orders are a miniaturisation of 'multiset path orders',"
                          , "restricted so that compatibility assesses a polynomial bound on the innermost runtime-complexity." ]
                , unwords [ "The implementation for DP problems additionally employs argument filterings."]]
        SPOP -> [ unwords [ "This processor implements orientation of the input problem using 'polynomial path orders'"
                         , "with product extension, c.f. processor 'popstar'."]]


    type ArgumentsOf PopStar = Arg Bool :+: Arg Bool :+: Arg (Maybe Nat)

    instanceName inst = show $ ppname <+> ppargs
        where ppname = 
                case knd of 
                  LMPO -> text "Lightweight Multiset Path Order"
                  POP -> text "Polynomial Path Order"
                  SPOP | wsc -> text "Small Polynomial Path Order"
                       | otherwise -> text "Polynomial Path Order"
              ppargs | null features = PP.empty
                     | otherwise     = parens $ hcat $ punctuate (text ",") features
                where features = [text n 
                                 | n <- catMaybes [ whenTrue ((knd /= SPOP) && wsc) "WSC"
                                                 , whenTrue ps "PS"
                                                 , whenTrue (knd == SPOP && not wsc) "PROD"
                                                 , (\ (Nat bnd) -> show bnd ++ "-bounded") `fmap` mbnd ] ]
                      whenTrue True  n = Just n
                      whenTrue False _ = Nothing
              knd = kind $ S.processor inst
              ps :+: wsc :+: mbnd = S.processorArgs inst

    arguments p = 
      case kind p of 
        LMPO    -> argPS 
                  :+: argWSC 
                  :+: argDeg
        POP     -> argPS { A.defaultValue = True} 
                  :+: argWSC 
                  :+: argDeg        
        SPOP    -> argPS { A.defaultValue = True}
                  :+: argWSC { A.defaultValue = True} 
                  :+: argDeg

    type ProofOf PopStar = OrientationProof PopStarOrder
    solve inst prob = case (Prob.startTerms prob, Prob.strategy prob) of 
                     ((BasicTerms _ _), Innermost) -> orientProblem inst Nothing prob
                     _                             -> return (Inapplicable "Processor only applicable for innermost runtime complexity analysis")

    solvePartial inst rs prob = 
      case (Prob.startTerms prob, Prob.strategy prob) of 
        ((BasicTerms _ _), Innermost) -> mkPP `liftM` orientProblem inst (Just rs) prob
        _                             -> return $ mkPP $ Inapplicable "Processor only applicable for innermost runtime complexity analysis"
      where sig = Prob.signature prob
            mkPP proof = P.PartialProof { P.ppInputProblem  = prob
                                        , P.ppResult        = proof
                                        , P.ppRemovableDPs  = sdps
                                        , P.ppRemovableTrs  = strs }
              where (sdps, strs) = partition marked sr
                    sr = case proof of 
                           (Order p) -> Trs.toRules $ popStrictlyOriented p
                           _         -> []
                    marked r = 
                      case root (lhs r) of 
                        Right f -> isMarked sig f
                        Left  _ -> False
                      

popstarProcessor :: S.StdProcessor PopStar
popstarProcessor = S.StdProcessor (PopStar POP)

ppopstarProcessor :: S.StdProcessor PopStar
ppopstarProcessor = S.StdProcessor (PopStar SPOP)

lmpoProcessor :: S.StdProcessor PopStar
lmpoProcessor = S.StdProcessor (PopStar LMPO)

-- | This processor implements polynomial path orders.
popstar :: S.ProcessorInstance PopStar
popstar = popstarProcessor `S.withArgs` (False :+: False :+: Nothing)

-- | This processor implements lightweight multiset path orders.
lmpo :: S.ProcessorInstance PopStar
lmpo = lmpoProcessor `S.withArgs` (False :+: False :+: Nothing)

-- | This processor implements polynomial path orders with parameter substitution.
popstarPS :: S.ProcessorInstance PopStar
popstarPS = popstarProcessor `S.withArgs` (True :+: False :+: Nothing)

-- | This processor implements small polynomial path orders (polynomial path orders with product extension and weak safe composition) 
      --   which allow to determine the degree of the obtained polynomial certificate.
popstarSmall :: Maybe Int -> S.ProcessorInstance PopStar
popstarSmall mi = ppopstarProcessor `S.withArgs` (False :+: True :+: (nat `liftM` mi))

-- | This processor is like 'popstarSmall' but incorporates parameter substitution addidionally.
popstarSmallPS :: Maybe Int -> S.ProcessorInstance PopStar
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


orientProblem :: P.SolverM m => S.TheProcessor PopStar -> Maybe P.SelectorExpression -> Problem -> m (OrientationProof PopStarOrder)
orientProblem inst mruleselect prob = maybe Incompatible Order `liftM` slv 
                                    
    where knd = kind $ S.processor inst
          allowPS :+: forceWSC :+: bnd = S.processorArgs inst
          allowAF   = (isDP && knd /= LMPO && Trs.isEmpty (Prob.strictTrs prob))
          allowMR   = knd == LMPO 
          forcePROD = knd == SPOP          
          isDP      = Prob.isDPProblem prob
          
          quasiConstrs = quasiConstructorsFor prob
          quasiDefineds = Trs.definedSymbols allrules \\ quasiConstrs
          
          allrules = Prob.allComponents prob
          sig      = Prob.signature prob
          
          slv | isDP      = solveDP 
              | otherwise = solveDirect
          
          solveDP = solveConstraint form initial mkOrd
              where mkOrd (us :&: sm :&: rs :&: prec :&: af :&: Sr sr) = 
                      PopOrder { popSafeMapping       = sm
                               , popPrecedence        = prec
                               , popRecursives        = rs
                               , popArgumentFiltering = Just af 
                               , popInputProblem      = prob 
                               , popInstance          = inst 
                               , popUsableSymbols     = us 
                               , popStrictlyOriented  = sr }
                    initial  = UREnc.initialUsables prob
                               :&: SMEnc.empty sig quasiConstrs 
                               :&: PrecEnc.initialRecursiveSymbols                                                         
                               :&: PrecEnc.initial sig 
                               :&: AFEnc.initial sig
                               :&: initialStrictRules 

          solveDirect = solveConstraint form initial mkOrd
              where mkOrd (sm :&: rs :&: prec :&: Sr sr) = 
                      PopOrder { popSafeMapping       = sm
                               , popPrecedence        = prec
                               , popRecursives        = rs
                               , popArgumentFiltering = Nothing
                               , popInputProblem      = prob 
                               , popInstance          = inst 
                               , popUsableSymbols     = Set.toList $ Trs.definedSymbols $ Prob.trsComponents prob 
                               , popStrictlyOriented  = sr}
                    initial             = SMEnc.empty sig quasiConstrs 
                                          :&: PrecEnc.initialRecursiveSymbols
                                          :&: PrecEnc.initial sig
                                          :&: initialStrictRules

          solveConstraint :: (S.Decoder e a) => P.SolverM m => MemoFormula PopArg MiniSatSolver MiniSatLiteral -> e -> (e -> b) -> m (Maybe b)
          solveConstraint constraint initial makeResult = 
              do r <- P.minisatValue (toFormula constraint >>= addFormula) initial
                 return $ makeResult `liftM` r
          
          form = validPrecedence -- fm maybeOrientable 
                 && (fm allowAF --> validArgumentFiltering)
                 && validUsableRules
                 && orderingConstraints allrules allrules
                 && orientAllUsableWeak
                 -- && orientAtleastOne
                 && orientSelectedStrict (fromMaybe selectStricts mruleselect)
                       where selectStricts = P.BigAnd $ [ P.SelectDP d | d <- Trs.rules $ Prob.strictDPs prob]
                                                        ++ [ P.SelectTrs d | d <- Trs.rules $ Prob.strictTrs prob]
                 
          usable = return . UREnc.usable prob
          
          -- orientAtleastOne = bigOr [ atom (strictlyOriented r) | r <- Trs.toRules $ Prob.strictComponents prob]
          orientAllUsableWeak = bigAnd [not (usable r) || atom (strictlyOriented r) || atom (weaklyOriented r) | r <- rules $ allrules]
          orientSelectedStrict (P.SelectDP r) = atom (strictlyOriented r)
          orientSelectedStrict (P.SelectTrs r) = atom (strictlyOriented r)
          orientSelectedStrict (P.BigAnd es) = bigAnd [ orientSelectedStrict e | e <- es]
          orientSelectedStrict (P.BigOr es) = bigOr [ orientSelectedStrict e | e <- es]          
          
          fs = Set.toList $ Trs.functionSymbols allrules
          
          nonCollapsingAf = bigAnd [ not (AFEnc.isCollapsing f) | f <- fs, isMarked sig f]
          
          validArgumentFiltering = 
            return $ AFEnc.validSafeArgumentFiltering fs sig
                     && (case bnd of 
                           Just (Nat 0) -> nonCollapsingAf
                           _            -> top)
          
          validPrecedence = 
            liftSat (PrecEnc.validPrecedenceM (Set.toList quasiDefineds) (adjustRecdepth `liftM` bnd))
            where adjustRecdepth (Nat b) 
                    | allCompoundsMonadic prob = b
                    | allowAF = floor (fromIntegral b / 2 :: Double)
                    | otherwise = b
                    
          validUsableRules = 
            liftSat $ toFormula $ UREnc.validUsableRulesEncoding prob isUnfiltered                    
              where isUnfiltered f i | allowAF   = AFEnc.isInFilter f i
                                     | otherwise = top
                                                 
          orderingConstraints srules eqrules = 
            bigAnd [ atom (strictlyOriented r) --> lhs r `pop` rhs r | r <- rules srules]
            && bigAnd [ atom (weaklyOriented r) --> lhs r `eq` rhs r | r <- rules eqrules]
              where pop s t = orient preds (Gt s t)
                    eq s t  = orient preds (Eq s t)
                    preds = 
                      Predicates { definedP    = defP
                                 , collapsingP = colP
                                 , inFilterP     = if allowAF then AFEnc.isInFilter else const . const top
                                 , safeP         = \ f i -> not (defP f) || SMEnc.isSafeP f i
                                 , precGtP       = \ f g -> defP f && (not (defP g) || f `PrecEnc.precGt` g)
                                 , precEqP       = \ f g -> not (compP f || compP g)
                                                            && ((not (defP f) && not (defP g)) 
                                                                || (defP f && defP g && f `PrecEnc.precEq` g))
                                 , allowMulRecP  = fm allowMR
                                 , allowPsP      = fm allowPS
                                 , weakSafeCompP = fm forceWSC
                                 , prodExtP      = fm forcePROD
                                 } 
                    defP f = fm $ f `Set.member` quasiDefineds
                    compP f = fm $ isCompound sig f
                    -- markeds = Trs.definedSymbols dps
                    -- colP f | allowAF && forceWSC && forcePROD = if f `Set.member` markeds
                    --                                           then bot 
                    --                                           else AFEnc.isCollapsing f
                    colP f | allowAF = AFEnc.isCollapsing f
                           | otherwise = bot
                      
                     
                                                 


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
