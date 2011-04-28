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
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE FlexibleContexts #-}

module Tct.Method.Uncurry
where
import Prelude hiding (uncurry)
import Data.Map (Map)
import Control.Monad
import qualified Data.Map as M
import Data.Typeable
import Data.Maybe (fromMaybe)

import Termlib.Problem hiding (Strategy, variables, strategy)
import qualified Termlib.Problem as Prob
import qualified Termlib.Rule as R
import Termlib.Variable (canonical)
import Termlib.FunctionSymbol (Signature, Symbol, SignatureMonad, Attributes(..))
import qualified Termlib.FunctionSymbol as F
import Termlib.Signature (runSignature )
import Termlib.Term (Term(..))
import Termlib.Utils (PrettyPrintable(..))
import qualified Termlib.Trs as Trs
import Termlib.Trs (Trs(..))

import Tct.Processor.Transformations as T
import qualified Tct.Processor as P
import Tct.Processor (Answerable (..), Answer (..))
import Tct.Processor.Args as A
import Text.PrettyPrint.HughesPJ hiding (empty)

data Uncurry = Uncurry deriving (Show,Typeable)

data UncurryProof = UncurryProof { inputProblem :: Problem
                                 , newSignature :: Signature
                                 , uncurryTrs   :: Trs 
                                 , uncurriedTrs :: Trs}
                  | NotUncurryable { reason :: String }


instance PrettyPrintable UncurryProof where 
    pprint (NotUncurryable r) = text "The system cannot be uncurried since given TRS is" <+> text r <> text "."
    pprint proof | Trs.isEmpty $ uncurriedTrs proof = text "The given TRS is empty, hence nothing to do." 
                 | otherwise = text "We uncurry the input using the following uncurry rules."
                   $+$ (nest 2 $ pptrs $ uncurryTrs proof)
             where pptrs trs = pprint (trs,sig,vars)
                   sig = newSignature proof
                   vars = Prob.variables $ inputProblem proof


instance P.Processor sub => Answerable (T.TProof Uncurry sub) where
    answer = T.answerTProof answer' 
        where answer' (NotUncurryable _) _        = MaybeAnswer
              answer' _                  [(_,ps)] = answer ps
              answer' _                  _        = error "Tct.Method.Uncurry: Uncurry proof with wrong number of subproblems received"

instance T.Verifiable UncurryProof

instance P.Processor sub => PrettyPrintable (T.TProof Uncurry sub) where
    pprint = prettyPrintTProof

instance T.Transformer Uncurry where
    type T.ArgumentsOf Uncurry = A.Unit
    type T.ProofOf     Uncurry = UncurryProof
    name Uncurry = "uncurry"
    description Uncurry = [ "This processor implements 'Uncurrying' for left-head-variable-free ATRSs"]
    arguments Uncurry = A.Unit
    transform _ prob =
        return $ case (relation prob) of
                   (Standard (Trs []))  -> T.Success p (enumeration' [prob])
                       where p = UncurryProof { inputProblem = prob
                                              , uncurryTrs   = Trs.empty
                                              , uncurriedTrs = Trs.empty 
                                              , newSignature = F.emptySignature}

                   (Standard trs) -> case applicativeSignature (Prob.signature prob) trs of 
                                       Nothing   -> T.Failure $ NotUncurryable {reason = "non applicative"}
                                       Just asig -> if not $ isLeftHeadVariableFree trs 
                                                    then T.Failure $ NotUncurryable {reason = "not left head variable free"}
                                                    else T.Success p (enumeration' [prob']) 
                                           where p = UncurryProof { inputProblem = prob
                                                                  , uncurryTrs   = ucTrs
                                                                  , uncurriedTrs = uncurried 
                                                                  , newSignature = sig}
                                                 ((ucTrs,uncurried), sig) = runSignature (mkUncurry asig (etaSaturate asig trs)) $ F.emptySignature
                                                 prob' = prob{relation=Standard (uncurried `Trs.union` ucTrs), signature=sig}
                   _               ->  T.Failure $ NotUncurryable { reason = "Uncurry for DP problems not implemented" }

uncurryProcessor :: TransformationProcessor Uncurry P.AnyProcessor
uncurryProcessor = transformationProcessor Uncurry

uncurry :: (P.Processor sub) => P.InstanceOf sub -> P.InstanceOf (TransformationProcessor Uncurry sub)
uncurry = transformationProcessor Uncurry `T.calledWith` ()


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
isLeftHeadVariableFree = Trs.allrules (lhvfree . R.lhs)
    where lhvfree (Var _)             = True
          lhvfree (Fun _ ((Var _):_)) = False
          lhvfree (Fun _ ts)          = all lhvfree ts


applicativeSignature :: Signature -> Trs -> Maybe AppSignature
applicativeSignature sig trs = case Trs.foldlRules f (Just (Nothing, M.empty)) trs of
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
mkUncurryTrs asig trs = Trs `liftM` mapM mkRule (rules trs)
    where mkRule (R.Rule lhs rhs) = do lhs' <- mk lhs
                                       rhs' <- mk rhs
                                       return $ R.Rule lhs' rhs'
          mk = fresh . uncurry
          appsym      = appSymbol asig
          s `apply` t = Fun appsym [s,t] 
          symOf g ar = do attribs <- F.getAttributes g 
                          case M.lookup g $ consts asig of 
                                 Just (gattribs,_) -> F.maybeFresh (alterAttributes ar gattribs) 
                                 Nothing           -> error $ show $ F.symIdent attribs
          -- symOf g ar = F.maybeFresh (alterAttributes ar gattribs) 
          --     where gattribs = case M.lookup g $ consts asig of 
          --                        Just (attribs,_) -> attribs
          --                        Nothing          -> error $ show g

          uncurry (Fun _ [t1,t2]) = case u1 of 
                                      Var{}     -> u1 `apply` u2
                                      Fun g u1s | appArity asig g > length u1s  -> Fun g (u1s ++ [u2])
                                                | otherwise                     -> u1 `apply` u2
              where u1 = uncurry t1
                    u2 = uncurry t2
          uncurry t               =  t
          fresh v@(Var _)               = return v
          fresh (Fun g ts) | g == appsym = fresh' g
                           | otherwise  = symOf g (length ts) >>= fresh'
              where fresh' g' = Fun g' `liftM` mapM fresh ts


mkUncurry :: AppSignature -> Trs -> SignatureMonad (Trs,Trs)
mkUncurry asig trs = do appsym <- F.maybeFresh $ F.defaultAttribs appName 2
                        let asig' = case asig of AppSignature (_,attribs) cs -> AppSignature (appsym,attribs) cs
                        us <- mkUncurrySystem asig'
                        uc <- mkUncurryTrs asig' trs
                        return $ (us,uc)
    where appName = case asig of AppSignature (_,attribs) _ -> F.symIdent attribs

