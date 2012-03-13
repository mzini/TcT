{- | 
Module      :  Tct.Method.Uncurry
Copyright   :  (c) Martin Avanzini <martin.avanzini@uibk.ac.at>, 
               Georg Moser <georg.moser@uibk.ac.at>, 
               Andreas Schnabl <andreas.schnabl@uibk.ac.at>
License     :  LGPL (see COPYING)

Maintainer  :  Martin Avanzini <martin.avanzini@uibk.ac.at>
Stability   :  unstable
Portability :  unportable      

This module implements the /uncurrying/ transformation.
-}

{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE FlexibleContexts #-}

module Tct.Method.Uncurry
       (
         uncurry
         -- * Proof Object
       , UncurryProof (..)
         -- * Processor
       , uncurryProcessor
       , Uncurry
       ) 
where
import Prelude hiding (uncurry)
import Data.Map (Map)
import Control.Monad
import qualified Data.Map as M
import Data.Typeable
import Data.Maybe (fromMaybe)
import qualified Data.Foldable as Fold

import Termlib.Problem hiding (Strategy, variables, strategy)
import qualified Termlib.Problem as Prob
import qualified Termlib.Rule as R
import Termlib.Variable (canonical)
import Termlib.FunctionSymbol (Signature, Symbol, SignatureMonad, Attributes(..))
import qualified Termlib.FunctionSymbol as F
import Termlib.Signature (runSignature, getSignature)
import Termlib.Term (Term(..))
import Termlib.Utils (PrettyPrintable(..),Enumerateable(..), paragraph)
import qualified Termlib.Trs as Trs
import Termlib.Trs (Trs)

import qualified Tct.Processor.Transformations as T
import qualified Tct.Processor as P
import Tct.Processor.Args as A
import Tct.Utils.Enum (enumeration')
import Text.PrettyPrint.HughesPJ hiding (empty)
import Tct.Certificate (constant, certified)

data Uncurry = Uncurry deriving (Show,Typeable)

data UncurryProof = UncurryProof { inputProblem    :: Problem
                                 , newSignature    :: Signature
                                 , uncurryTrs      :: Trs 
                                 , uncurriedStrict :: Trs
                                 , uncurriedWeak   :: Trs }
                  | NotUncurryable { reason :: String }
                  | EmptyStrictRules


instance T.TransformationProof Uncurry where
    answer proof = case (T.transformationProof proof, T.subProofs proof) of 
                     (NotUncurryable _, _             ) -> P.MaybeAnswer
                     (EmptyStrictRules, _             ) -> P.CertAnswer $ certified (constant, constant)
                     (_               , [(_,subproof)]) -> P.answer subproof
                     (_               , _             ) -> P.MaybeAnswer
    pprintTProof _ _ proof _ =
        case proof of 
          NotUncurryable r -> paragraph ("The system cannot be uncurried since given TRS is " ++ r ++ ".")
          EmptyStrictRules -> paragraph "The strict rules are empty."
          _                -> paragraph "We uncurry the input using the following uncurry rules."
                             $+$ text ""
                             $+$ (nest 2 $ pptrs $ uncurryTrs proof)
                             
             where pptrs trs = pprint (trs,sig,vars)
                   sig = newSignature proof
                   vars = Prob.variables $ inputProblem proof

instance T.Transformer Uncurry where
    type T.ArgumentsOf Uncurry = A.Unit
    type T.ProofOf     Uncurry = UncurryProof
    name Uncurry = "uncurry"
    description Uncurry = [ "This processor implements 'Uncurrying' for left-head-variable-free ATRSs"]
    arguments Uncurry = A.Unit
    transform _ prob | isDPProblem prob = return $ T.NoProgress $ NotUncurryable { reason = "Uncurry for DP problems not implemented" }
                     | Trs.isEmpty (strictTrs prob) = return $ T.NoProgress $ EmptyStrictRules
                     | otherwise = return $ case applicativeSignature (Prob.signature prob) (trsComponents prob) of 
                                     Nothing   -> T.NoProgress $ NotUncurryable {reason = "non applicative"}  
                                     Just asig -> if not $ isLeftHeadVariableFree (trsComponents prob)
                                                    then T.NoProgress $ NotUncurryable {reason = "not left head variable free"}
                                                    else T.Progress p (enumeration' [prob']) 
                                           where m = do appsym <- F.maybeFresh $ F.defaultAttribs appName 2
                                                        let asig' = case asig of AppSignature (_,attribs) cs -> AppSignature (appsym,attribs) cs
                                                        ustrct <- mkUncurryTrs asig' (saturated strct)
                                                        uweak <- mkUncurryTrs asig' (saturated weak)
                                                        us <- mkUncurrySystem asig'
                                                        sig <- getSignature
                                                        return UncurryProof { inputProblem = prob
                                                                            , uncurryTrs   = us
                                                                            , uncurriedStrict = ustrct
                                                                            , uncurriedWeak   = uweak
                                                                            , newSignature = sig }

                                                 appName = case asig of AppSignature (_,attribs) _ -> F.symIdent attribs
                                                 saturated = etaSaturate asig

                                                 strct  = strictTrs prob
                                                 weak   = weakTrs prob
                                                 (p, _) = runSignature m F.emptySignature
                                                 prob'  = prob { strictTrs = uncurriedStrict p
                                                               , weakTrs   = uncurriedWeak p `Trs.union` uncurryTrs p
                                                               , signature = newSignature p }


uncurryProcessor :: T.Transformation Uncurry P.AnyProcessor
uncurryProcessor = T.Transformation Uncurry

-- | Uncurrying for full and innermost rewriting. Note that this processor fails on dependency pair problems.
uncurry :: T.TheTransformer Uncurry
uncurry = T.Transformation Uncurry `T.withArgs` ()


data AppSignature = AppSignature {app :: (Symbol,Attributes), consts :: Map Symbol (Attributes,Int)} deriving Show


appSymbol :: AppSignature -> Symbol
appSymbol = fst . app

appArity :: AppSignature -> Symbol -> Int
appArity asig sym = case M.lookup sym (consts asig) of 
                      Just (_,i) -> i
                      Nothing    -> error "Uncurry.appArity: cannot find symbol"

applicativeArity :: AppSignature -> Term -> Int
applicativeArity asig (Fun g []) = case M.lookup g $ consts asig of 
                                     Just (_,ar) -> ar
                                     _           -> error "Uncurry.applicativeArity: cannot find constant in applicative signature"
applicativeArity asig (Fun _ [a,_]) = applicativeArity asig a - 1
applicativeArity _    _             = error "Uncurry.applicativeArity: non-applicative term given"

isLeftHeadVariableFree :: Trs -> Bool
isLeftHeadVariableFree = Fold.all (lhvfree . R.lhs)
    where lhvfree (Var _)             = True
          lhvfree (Fun _ ((Var _):_)) = False
          lhvfree (Fun _ ts)          = all lhvfree ts


applicativeSignature :: Signature -> Trs -> Maybe AppSignature
applicativeSignature sig trs = case Fold.foldl f (Just (Nothing, M.empty)) trs of
                                 Just (Just appsym, asig) -> Just $ AppSignature (appsym, attribs) asig
                                     where Just attribs = F.lookup appsym sig
                                 Nothing         -> Nothing
                                 Just _          -> Nothing
    where f Nothing     _                 = Nothing
          f (Just (mapp,syms))  (R.Rule lhs rhs)  = fTerm lhs (mapp,syms) >>= fTerm rhs

          fTerm (Var _)       r                                          = Just $ r
          fTerm (Fun g [])    r                                          = Just $ inst g 0 r
          fTerm t@(Fun g _)   (Nothing, syms)                            = fTerm t ((Just g), syms)
          fTerm (Fun g [a,b]) (mapp@(Just appsym), syms)  | appsym /= g = Nothing
                                                          | otherwise  = case leftmst a 1 of
                                                                           Just (c,i) -> rec >>= return . (inst c i)
                                                                           Nothing    -> rec
                                                       where rec = fTerm a (mapp,syms) >>= fTerm b
          fTerm _             _                                          = Nothing

          leftmst (Var _)       _ = Nothing
          leftmst (Fun g [])    i = Just (g,i)
          leftmst (Fun _ (e:_)) i = leftmst e (i + 1)

          inst g ar (mapp,syms) = (mapp, M.alter updateVal g syms)
              where updateVal Nothing = Just (attribs,ar) where 
                        attribs = fromMaybe err (F.lookup g sig)
                        err     = error "Uncurry.applicativeSignature: cannot find apply-symbol in signature"
                    updateVal (Just (attribs,ar')) = Just (attribs, (max ar' ar))



etaSaturate :: AppSignature -> Trs -> Trs
etaSaturate asig = Trs.mapRules saturateRule 
    where saturateRule (R.Rule l r) = R.Rule (saturate aar l) (saturate aar r)
              where aar = applicativeArity asig l
                    saturate 0 t = t
                    saturate n t = saturate (n - 1) (Fun appsym [t, Var $ canonical n])
                    (appsym,_) = app asig

alterAttributes ::  Int -> F.Attributes -> F.Attributes
alterAttributes ar attribs = attribs{symArity = ar, symIdent=symIdent attribs ++ num}
    where num | ar == 0    = ""
              | otherwise = "_" ++ show ar

mkUncurrySystem :: AppSignature -> SignatureMonad Trs
mkUncurrySystem asig = Trs.Trs `liftM` foldM mk [] (M.toList $ consts asig)
    where (asym,_) = app asig
          mk rs (_, (attribs, ar)) = do ais <- forM [0..ar] mkAi
                                        return $ (mkRules ais) ++ rs
              where mkAi i = do sym <- F.maybeFresh $ alterAttributes i attribs
                                return (sym, i)
                    mkRules []                          = []
                    mkRules [_]                         = []
                    mkRules ((a_i, i) : ((a_i',i') : ais)) = R.Rule lhs rhs : (mkRules ((a_i',i') : ais))
                        where lhs = Fun asym [(mkTerm a_i i), cvar $ i + 1] 
                              rhs = (mkTerm a_i' i')
                              mkTerm a_j j  = Fun a_j $ take j cvars
                              cvar          = Var . canonical
                              cvars = [cvar j | j <- [1..]]

mkUncurryTrs :: AppSignature -> Trs -> SignatureMonad Trs
mkUncurryTrs asig trs = Trs.fromRules `liftM` mapM mkRule (Trs.toRules trs)
    where mkRule (R.Rule lhs rhs) = do lhs' <- mk lhs
                                       rhs' <- mk rhs
                                       return $ R.Rule lhs' rhs'
          mk = fresh . uc
          appsym      = appSymbol asig
          fakeApp     = invEnum (-1 :: Int)
          s `apply` t = Fun fakeApp [s,t] 
          symOf g ar = case M.lookup g $ consts asig of 
                         Just (gattribs,_) -> F.maybeFresh (alterAttributes ar gattribs) 
                         Nothing           -> error "Uncurry: symbol not found"

          uc (Fun _ [t1,t2]) = case u1 of 
                                 Var{}     -> u1 `apply` u2
                                 Fun g u1s | g == fakeApp                  -> u1 `apply` u2
                                           | appArity asig g > length u1s  -> Fun g (u1s ++ [u2])
                                           | otherwise                     -> u1 `apply` u2
              where u1 = uc t1
                    u2 = uc t2
          uc t               =  t
          fresh v@(Var _)                = return v
          fresh (Fun g ts) | g == fakeApp = fresh' appsym
                           | otherwise   = symOf g (length ts) >>= fresh'
              where fresh' g' = Fun g' `liftM` mapM fresh ts




