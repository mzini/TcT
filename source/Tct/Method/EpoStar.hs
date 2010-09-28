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
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE ParallelListComp #-}

module Tct.Method.EpoStar 
    ( epostar
    , epostarProcessor
    , EpoProof (..)
    )
where

--import Debug

import Data.Set as Set
import qualified Data.Map as Map
import Data.Maybe (fromMaybe)
import Control.Monad (foldM, liftM, liftM2, join)
import Control.Monad.Trans (liftIO)
import qualified Control.Monad.State.Lazy as State
import qualified Control.Monad.State.Class as StateClass

import Prelude hiding (and, or, not)
import Text.PrettyPrint.HughesPJ hiding (empty)
import Data.Typeable
import Termlib.Term
import Termlib.Trs (Trs(..))
import qualified Termlib.Trs as Trs
import Termlib.FunctionSymbol (Symbol, arity, Signature)
import Termlib.Utils (PrettyPrintable(..))
import qualified Termlib.Precedence as Prec
import Termlib.Precedence (Order (..))
import qualified Termlib.Problem as Prob
import Termlib.Problem (Strategy(..), StartTerms(..))
import qualified Termlib.Rule as R
import Termlib.Variable (Variables)

import qualified Tct.Processor as P
import qualified Tct.Processor.Standard as S
import Tct.Certificate
import Tct.Proof
import Tct.Processor.Orderings
import Tct.Processor.Args
import Tct.Processor.Args.Instances ()
import qualified Tct.Processor.Args as A
import qualified Tct.Encoding.SafeMapping as SM
-- import Satchmo.Binary.Op.Flexible
import Satchmo.Boolean
import Satchmo.Relation
import Satchmo.Binary.Op.Fixed (number, eq, gt)
import Satchmo.Counting (exactly)
import Satchmo.Code
import qualified Satchmo.Solver.Minisat as Minisat
import Satchmo.SAT
import qualified Data.Array as A
import Data.Map as Map hiding ((!))
import qualified Prelude as Prelude

--------------------------------------------------------------------------------
-- helpers

find :: Ord a => a -> Map a v -> v
find e = fromMaybe (error "EpoStar.find") . Map.lookup e

monadic2 :: Monad m => (a -> b -> m c) -> (m a -> m b -> m c)
monadic2 f a b = join $ liftM2 f a b

-- monadic3 :: Monad m => (a -> b -> c -> m d) -> (m a -> m b -> m c -> m d)
-- monadic3 f a b c = join $ liftM3 f a b c

--------------------------------------------------------------------------------
-- satchmo stuff

imp :: MonadSAT m => Boolean -> Boolean -> m Boolean
imp a b = or [not a, b]

iff :: MonadSAT m => Boolean -> Boolean -> m Boolean
iff a b = andM [ imp a b
               , imp b a]

ite :: MonadSAT m => Boolean -> Boolean -> Boolean -> m Boolean
ite g t e = monadic and [ imp g t
                        , imp (not g) e]

andM :: MonadSAT m =>  [m Boolean] -> m Boolean
andM = monadic and

orM :: MonadSAT m => [m Boolean] -> m Boolean
orM = monadic or

impM :: MonadSAT m => m Boolean -> m Boolean -> m Boolean
impM = monadic2 imp

-- iffM :: MonadSAT m => m Boolean -> m Boolean -> m Boolean
-- iffM = monadic2 iff

bijection :: (MonadSAT m, A.Ix a, A.Ix b) => ((a,b),(a,b)) -> m (Relation a b)
-- stolen from http://hackage.haskell.org/package/satchmo-examples
bijection bnd = do
    let ((u,l),(o,r)) = bnd
    a <- relation bnd
    -- official encoding: exactly one per row, exactly one per column
    sequence_ $ do
        x <- A.range (u,o)
        return $ monadic assert $ return $ exactly 1 $ do y <- A.range (l,r) ; return $ a!(x,y)
    sequence_ $ do
        y <- A.range (l,r)
        return $ monadic assert $ return $ exactly 1 $ do x <- A.range (u,o) ; return $ a!(x,y)
    return a        

-- memoization

newtype Memo arg m r = Memo {
      runMemo:: State.StateT (Map.Map arg Boolean) m r
    } deriving (Monad, Functor, StateClass.MonadState (Map.Map arg Boolean), MonadSAT)

run :: Monad m => Memo arg m r -> m r
run m = fst `liftM` State.runStateT (runMemo m) Map.empty


memoized :: (MonadSAT m, Ord arg) => (arg -> Memo arg m Boolean) -> (arg -> Memo arg m Boolean)
memoized f a = do ls <- State.get
                  case Map.lookup a ls of 
                    Nothing -> do b <- f a
                                  State.modify (Map.insert a b)
                                  return b
                    Just b  -> return b 

--------------------------------------------------------------------------------
-- epostar proof object

newtype ArgumentPermutation = AP (Map Symbol [Int])

instance PrettyPrintable (ArgumentPermutation,Sig) where 
  pprint (AP m, sign) = fsep $ punctuate (text ",") [ pp sym | sym <- Set.toList $ defineds sign]
    where pp sym = text "mu" <> parens (pprint (sym, sig sign)) <+> text "=" 
                   <+> (brackets . fsep . punctuate (text ",") $ [ text $ show i | i <- find sym m])


data EpoProof = EpoProof Trs SM.SafeMapping Prec.Precedence ArgumentPermutation Sig

instance PrettyPrintable EpoProof where
    pprint (EpoProof trs sm prec perm sign) = ppstrict $$ ppsm $$ ppperm $$ ppprec 
      where ppsm           = text "Safe Mapping:" $$ (nest 1 $ pprint $ sm)
            ppprec         = text "Precedence:" $$ (nest 1 $ pprint $ prec)
            ppperm         = text "Argument Permutation:" $$ (nest 1 $ pprint (perm,sign))
            ppstrict       = text "Strict Rules in Predicative Notation:" 
                             $$ (nest 1 $ pprint $ (trs, sig sign, vars sign, sm))

instance (Answerable EpoProof) where 
    answer _ = CertAnswer $ certified (unknown, expo $ Nothing)

-- instance ComplexityProof EpoProof


--------------------------------------------------------------------------------
-- processor

data EpoStar = EpoStar deriving (Show, Eq, Typeable)

instance S.StdProcessor EpoStar where
    name _ = "epo*"
    description _ = [ unlines [ "This processor implements orientation of the input problem using 'exponential path orders',"
                              , "a technique applicable for innermost runtime-complexity analysis."
                              , "Exponential path orders are a miniaturisation of 'lexicographic path orders',"
                              , "restricted so that compatibility assesses exponential runtime complexity."]]
    type S.ArgumentsOf EpoStar = Arg Bool

    instanceName inst = S.name (S.processor inst) 
                        ++ case S.processorArgs inst of {True -> "(extended composition)"; False -> ""}

    arguments _ = opt { A.name = "ecomp"
                      , A.description = unlines [ "If this flag is enabled, then the slightly more liberal composition scheme f(x;y) = h(g(;x);k(x;y)) is permitted."
                                                , "Currently it is not known whether this extension is sound"]
                      , A.defaultValue = False }

    type S.ProofOf EpoStar = OrientationProof EpoProof

    solve inst prob = case (Prob.startTerms prob, Prob.strategy prob, Prob.relation prob) of 
                        ((BasicTerms ds cs), Innermost, Prob.Standard trs) | Trs.isConstructor trs -> do r <- liftIO $ orientTrs sign ec trs
                                                                                                         case r of 
                                                                                                           Just (sm, (prec, mu)) -> return $ Order $ EpoProof trs sm prec mu sign
                                                                                                           Nothing               -> return Incompatible
                                                                           where sign = Sig { defineds = ds
                                                                                            , constructors = cs
                                                                                            , sig = Prob.signature prob
                                                                                            , vars = Prob.variables prob}
                                                                                 ec   = S.processorArgs inst
                        _                                                            -> return Incompatible

epostarProcessor :: S.Processor EpoStar
epostarProcessor = S.Processor EpoStar

epostar :: Bool -> P.InstanceOf (S.Processor EpoStar)
epostar ec = EpoStar `S.calledWith` ec

--------------------------------------------------------------------------------
-- encoding

data EpoOrder = Epo Term Term
              | Eposub Term Term
              | Eq Term Term deriving (Eq, Ord)

type EpoSAT r = Memo EpoOrder SAT r


type Precedence  = Order -> Boolean
data PrecedenceDecoder = PrecDecode (Map (Symbol, Symbol) (Boolean,Boolean)) Sig -- TODO: sehr stupide idee
type SafeMapping = Symbol -> Int -> Boolean -- (Relation Int ()) -- (Ix Symbol) not adequate
data SafeMappingDecoder = SMDecode (Map Symbol (Relation Int ())) Sig
type MuMapping   = Symbol -> (Relation Int Int)
data MuMappingDecoder = MuDecode (Map Symbol (Relation Int Int))

data Sig = Sig { defineds     :: Set Symbol
               , constructors :: Set Symbol
               , vars         :: Variables
               , sig          :: Signature} deriving Show
                               
isDefined :: Sig -> Symbol -> Bool
isDefined sign f = Set.member f $ defineds sign

isConstructor :: Sig -> Symbol -> Bool
isConstructor sign f = Set.member f $ constructors sign

isConstructorTerm :: Sig -> Term -> Bool
isConstructorTerm sign t = functionSymbols t `Set.isSubsetOf` constructors sign

ar :: Sig -> Symbol -> Int
ar sign f = arity (sig sign) f

symbols :: Sig -> [Symbol]
symbols sign = Set.toList (defineds sign) ++ Set.toList (constructors sign)


precedence :: Sig -> EpoSAT (Precedence, PrecedenceDecoder) 
precedence sign = do top <- constant True
                     bot <- constant False
                     let fs = Set.toList $ defineds sign
                         pairs = [(f,g) | f <- fs, g <- fs]
                         bits = ceiling $ (log $ fromIntegral $ length fs :: Double)
                     lvs <- foldM (\ m f -> number bits >>= \ n -> return $ Map.insert f n m) Map.empty fs
                     prec <- foldM (\ m (f,g) -> do let nf = find f lvs  
                                                        ng = find g lvs
                                                    gtp <- nf `gt` ng
                                                    eqp <- nf `eq` ng
                                                    return $ Map.insert (f,g) (gtp,eqp) m)
                         Map.empty 
                         pairs
                     let pr f g | f < g     = (f,g)
                                | otherwise = (g,f)
                         mkf (f :>: g) | f == g               = bot
                                       | isConstructor sign f = bot
                                       | isConstructor sign g = top
                                       | otherwise            = fst $ find (f,g) prec
                         mkf (f :~: g) | f == g               = top
                                       | cf && Prelude.not cg = bot
                                       | Prelude.not cf && cg = bot
                                       | cf && cg             = top
                                       | ar sign f /= ar sign g = bot
                                       | otherwise            = snd $ find (pr f g) prec
                             where cf = isConstructor sign f 
                                   cg = isConstructor sign g
                     
                     return $ (mkf, PrecDecode prec sign)

instance Decode PrecedenceDecoder Prec.Precedence where
    decode (PrecDecode m sign) = Prec.precedence (sig sign) `liftM` foldM mk [] (Map.toList m)
        where mk l ((f,g),b) = do (gtp,eqp) <- decode b
                                  return $ [ ord | (ord,setp) <- [(f :>: g,gtp), (f :~: g,eqp)], setp] ++ l

safeMapping :: Sig -> EpoSAT (SafeMapping, SafeMappingDecoder) 
safeMapping sign = do m <- foldM mk Map.empty (Set.toList $ defineds sign)
                      top <- constant True
                      return $ (\ f i -> if isConstructor sign f 
                                         then top
                                         else (fromMaybe err $ Map.lookup f m) ! (i,())
                               , SMDecode m sign)
    where err = error "safeMapping, symbol not known"
          mk m f = do r <- relation ((1,()),(ar sign f, ()))
                      return $ Map.insert f r m

instance Decode SafeMappingDecoder SM.SafeMapping where
    decode (SMDecode m sign)  = foldM mk initial (Map.toList m)
        where initial = SM.empty (sig sign) (constructors sign)
              mk sm (f, b) = do sps <- safes `liftM` decode b
                                return $ SM.setSafes f sps sm
              safes rel = [ i | ((i,()), isSafe) <- A.assocs rel, isSafe]

muMapping :: Sig -> EpoSAT (MuMapping, MuMappingDecoder)
muMapping sign = do m <- foldM mk Map.empty syms
                    return $ (\f -> find f m, MuDecode m)
    where syms = symbols sign
          mk m f = do let a = ar sign f
                      b <- bijection ((1,1),(a,a))
                      return $ Map.insert f b m

instance Decode MuMappingDecoder ArgumentPermutation where
    decode (MuDecode m) = AP `liftM` foldM mk Map.empty (Map.toList m)
        where mk m' (f,rel) = do (arr :: A.Array (Int,Int) Bool) <- decode rel
                                 let ((l,u),(r,o)) = A.bounds arr
                                     fnd k = head [i | i <- [l..r],  (A.!) arr (i,k) ]
                                 return $ Map.insert f (Prelude.map fnd [u..o]) m'

unorientable :: Sig -> Term -> Term -> Bool
unorientable sign u v = variables u `Set.isProperSubsetOf` variables v 
                        || (isConstructorTerm sign u && Prelude.not (isConstructorTerm sign v))

orient :: Bool -> Sig -> Precedence -> SafeMapping -> MuMapping -> (EpoOrder -> EpoSAT Boolean)
orient allowEcomp sign prec safe mu = memoized $ \ a -> case a of 
                                                          Epo s t    -> s `epoimp` t
                                                          Eposub s t -> s `eposubimp` t
                                                          Eq s t     -> s `equivimp` t
    where precM = return . prec
          s `epo` t    = orient allowEcomp sign prec safe mu (Epo s t)
          s `eposub` t = orient allowEcomp sign prec safe mu (Eposub s t)
          s `equiv` t  = orient allowEcomp sign prec safe mu (Eq s t)

          -- epo
          u `epoimp` v | u `isProperSupertermOf` v = constant True 
                       | unsatisfiable             = constant False 
                       | otherwise                 = orM [u `epo1` v, u `epo23` v]
              where unsatisfiable = unorientable sign u v 
                    epo1 (Fun _ ss) t = orM [ orM [ si `equiv` t, si `epo` t] | si <- ss]
                    epo1 _          _ = constant False

                    epo23 s@(Fun f ss) (Fun g ts) = do andM [ andM [ do epoorient <- s `epo` ti
                                                                        eposuborient <- s `eposub` ti
                                                                        ite (safe g i) epoorient eposuborient
                                                                            | (i,ti) <- tsi ]
                                                            , orM [ precM $ f :>: g, epo3]]
                        where ssi = [ (i, si) | i <- [1..] | si <- ss]
                              tsi = [ (i, ti) | i <- [1..] | ti <- ts]
                              epo3 | isDefined sign g && length ss == length ts && length ss > 0 = andM [ precM $ f :~: g , epolex 1]
                                   | otherwise = constant False
                              epolex k | length ssi < k = constant False
                                       | otherwise      = andM [ do cond <- and [mu f ! (i,k), mu g ! (j,k)]
                                                                    rec <- epolex (k+1)
                                                                    comp <- orM [ (si `eposub` tj) 
                                                                                , andM [ si `equiv` tj, return rec] ]
                                                                    concl <- ite (safe g j) rec comp
                                                                    cond `imp` concl
                                                                 | (i, si) <- ssi, (j, tj) <- tsi]
                    epo23 _ _ = constant False

          -- eposub
          u `eposubimp` v | unsatisfiable = constant False
                          | otherwise     = orM [u `eposub1` v, u `eposub2` v] 
              where unsatisfiable = unorientable sign u v 
                    
                    (Fun f ss) `eposub1` t = orM [ andM [maybeNormal i, orM [si `eposub` t, si `equiv` t]] | i <- [1..] | si <- ss]
                        where maybeNormal i | isDefined sign f = return $ not $ safe f i
                                            | otherwise        = constant True
                    _ `eposub1` _ = constant False
                    s@(Fun f _) `eposub2` (Fun g ts) | allowEcomp = andM [ precM $ f :>:g , andM [ andM [ return (safe g i), s `eposub` ti] | i <- [1..] | ti <- ts] ]
                                                     | otherwise  = constant False
                    _ `eposub2` _ = constant False

          -- equivalence
          u `equivimp` v | u == v    = constant True
                         | unsatisfiable = constant False
                         | otherwise = case (u,v) of
                                         (Var _, Var _) -> constant False -- u != v assumed
                                         (Fun f ss, Fun g ts) | unsat     -> constant False 
                                                              | otherwise -> monadic and [ return $ prec $ f :~: g
                                                                                        , andM [ and [mu f ! (i,k), mu g ! (j,k)] `impM` (si `equiv` tj)
                                                                                                 | (i,si) <- zip [1..] ss
                                                                                               , (j,tj) <- zip [1..] ts
                                                                                               , k <- [1..length ss]]]
                                                              where unsat = (length ss /= length ts) || (isConstructor sign f /= isConstructor sign g)
                                         _              -> constant False
              where unsatisfiable = unorientable sign u v 


orientTrs :: Sig -> Bool -> Trs -> IO (Maybe (SM.SafeMapping, (Prec.Precedence, ArgumentPermutation)))
orientTrs sign b (Trs rs) = Minisat.solve (run constraint)
    where constraint = do (sm, smdecode) <- safeMapping sign
                          (prec, precdecode) <- precedence sign
                          (mu, mudecode) <- muMapping sign
                          let epo s t = orient b sign prec sm mu (Epo s t)
                          monadic assert [consistent sm prec mu]
                          monadic assert [monadic and [ R.lhs r `epo` R.rhs r | r <- rs ]]
                          return $ decode (smdecode,(precdecode, mudecode))
          consistent safe prec mu =do andM [ do let af = ar sign f
                                                conc <- andM [ (and [mu f ! (i,k), mu g ! (j,k)]) `impM` (safe f i `iff` safe g j)
                                                               | i <-[1..af]
                                                             , j <- [1..af]
                                                             , k <- [1..af]]
                                                prec (f :~: g) `imp` conc
                                             | f <- defs, g <- defs
                                           , ar sign f == ar sign g -- f ~ g implies ar(f) = ar(g)
                                           ] 
              where defs = Set.toList $ defineds sign