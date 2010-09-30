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

module Tct.Method.Uncurry
where
import Prelude hiding (uncurry)
import Data.Map (Map)
import Control.Monad
import qualified Data.Map as M
import qualified Data.List as L
import Data.Typeable
import Data.Maybe (fromMaybe)

import Termlib.Problem hiding (Strategy, variables, strategy)
import qualified Termlib.Problem as Prob
import qualified Termlib.Rule as R
import Termlib.Variable (Variables, canonical)
import Termlib.FunctionSymbol (Signature, Symbol, SignatureMonad, Attributes(..))
import qualified Termlib.FunctionSymbol as F
import Termlib.Signature (runSignature )
import Termlib.Term (Term(..))
import Termlib.Utils (PrettyPrintable(..))
import qualified Termlib.Trs as Trs
import qualified Termlib.Term as T
import Termlib.Trs (Trs(..))

import Tct.Proof
import Tct.Certificate (uncertified)
import Tct.Processor.Transformations as T
import Text.PrettyPrint.HughesPJ hiding (empty)

data Uncurry = Uncurry deriving (Show,Typeable)

data UncurryProof = UncurryProof Signature Variables Trs Trs 
                  | NotUncurryable 

instance PrettyPrintable UncurryProof where 
    pprint (UncurryProof sig vars ucTrs uncurried) = text "We obtain the following uncurried TRS" 
                                                     $+$ (nest 2 $ pptrs uncurried)
                                                     $+$ text "Following uncurry rules were used:" 
                                                     $+$ (nest 2 $ pptrs ucTrs)
             where pptrs trs = pprint (trs,sig,vars)
    pprint NotUncurryable                            = text "The system cannot be uncurried"

instance Answerable sp => Answerable (T.TransformationProof UncurryProof sp) where
    answer (TransformationProof NotUncurryable _) = MaybeAnswer



data AppSignature = AppSignature {app :: (Symbol,Attributes), consts :: Map Symbol (Attributes,Int)} deriving Show

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
                                 Just _          -> error "Uncurry.applicativeSignature: weird things happened"
    where f Nothing     _                 = Nothing
          f (Just (mapp,syms))  (R.Rule lhs rhs)  = fTerm lhs (mapp,syms) >>= fTerm rhs

          fTerm (Var _)       r                                          = Just $ r
          fTerm (Fun g [])    r                                          = Just $ inst g 0 r
          fTerm t@(Fun g _)   (Nothing, syms)                            = fTerm t ((Just g), syms)
          fTerm (Fun g [a,b]) (mapp@(Just appsym), syms)  | appsym /= g  = Nothing
                                                          | otherwise = case leftmst a 1 of
                                                                          Just (c,i) -> rec >>= return . (inst c i)
                                                                          Nothing    -> rec
                                                       where rec = fTerm a (mapp,syms) >>= fTerm b
          fTerm _             _                                     = Nothing

          leftmst (Var _)       _ = Nothing
          leftmst (Fun g [])    i = Just (g,i)
          leftmst (Fun _ (e:_)) i = leftmst e (i + 1)

          inst g ar (mapp,syms) = (mapp, M.alter updateVal g syms)
              where updateVal Nothing = Just (attribs,ar) where 
                        attribs = fromMaybe err (F.lookup g sig)
                        err     = error "Uncurry.applicativeSignature: cannot find apply-symbol in signature"
                    updateVal (Just (attribs,ar')) = Just (attribs, (max ar' ar))


applicativeArity :: AppSignature -> Term -> Int
applicativeArity asig (Fun g []) = case M.lookup g $ consts asig of 
                                     Just (_,ar) -> ar
                                     _           -> error "Uncurry.applicativeArity: cannot find constant in applicative signature"
applicativeArity asig (Fun _ [a,_]) = applicativeArity asig a - 1
applicativeArity _    _             = error "Uncurry.applicativeArity: non-applicative term given"

etaSaturate :: AppSignature -> Trs -> Trs
etaSaturate asig = Trs.mapRules saturateRule 
    where saturateRule (R.Rule l r) = R.Rule (saturate aar l) (saturate aar r)
              where aar = applicativeArity asig l
                    saturate 0 t = t
                    saturate n t = saturate (n - 1) (Fun appsym [t, Var $ canonical n])
                    (appsym,_) = app asig

alterAttributes ::  Int -> F.Attributes -> F.Attributes
alterAttributes ar attribs = attribs{symArity = ar, symIdent=symIdent attribs ++ "_" ++ show ar}

uncurrySystem :: AppSignature -> SignatureMonad Trs
uncurrySystem asig = Trs.Trs `liftM` foldM mk [] (M.toList $ consts asig)
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

uncurryTrs :: AppSignature -> Trs -> SignatureMonad Trs
uncurryTrs asig trs = Trs `liftM` mapM mkRule (rules trs)
    where mkRule (R.Rule lhs rhs) = do lhs' <- mk lhs
                                       rhs' <- mk rhs
                                       return $ R.Rule lhs' rhs'
              where mk = uncurrySexpr . sexpr

          sexpr = rev . revSexpr
          revSexpr v@(Var _)    = v
          revSexpr g@(Fun _ []) = g
          revSexpr (Fun _ [a,b]) | isAtom a  = Fun undefined [revSexpr b, a]
                                 | otherwise = Fun undefined (revSexpr b : (T.immediateSubterms $ revSexpr a))
          revSexpr _            = error "Uncurry.uncurryTrs: non-applicative system given"
          isAtom (Var _)    = True
          isAtom (Fun _ []) = True
          isAtom _          = False

          rev (Fun a l) = Fun a [rev l_i | l_i <- L.reverse l]
          rev a         = a

          uncurrySexpr v@(Var _)        = return $ v
          uncurrySexpr (Fun g [])       = do g' <- symOf g 0
                                             return $ Fun g' []
          uncurrySexpr (Fun _ (v@(Var _):args)) = do args' <- uncurrySexprs args 
                                                     return $ Fun appsym (v : args')
          uncurrySexpr (Fun _ (Fun g []:args)) = do args' <- uncurrySexprs args 
                                                    g' <- symOf g (length args)
                                                    return $ Fun g' args'
          uncurrySexpr _                = error "Uncurry.uncurryTrs: non-left-head-variable free TRS"
          uncurrySexprs = mapM uncurrySexpr

          (appsym,_) = app asig
          symOf g ar = F.maybeFresh (alterAttributes ar gattribs) where Just (gattribs,_) = M.lookup g $ consts asig

uncurry :: AppSignature -> Trs -> SignatureMonad (Trs,Trs)
uncurry asig trs = do appsym <- F.maybeFresh $ F.defaultAttribs appName 2
                      let asig' = case asig of AppSignature (_,attribs) cs -> AppSignature (appsym,attribs) cs
                      us <- uncurrySystem asig'
                      uc <- uncurryTrs asig' trs
                      return (us,uc)
    where appName = case asig of AppSignature (_,attribs) _ -> F.symIdent attribs


instance Transformer Uncurry where
   transformerName _ _ = "Uncurrying"
   transform _ prob =
     case (relation prob) of
       (Standard (Trs []))  -> abortWith $ text $ "Uncurrying not applicable to empty TRS"
       (Standard trs) -> case applicativeSignature (Prob.signature prob) trs of 
                          Nothing   -> abortWith $ text $ "Uncurrying only applicable to applicative TRSs"
                          Just asig -> if not $ isLeftHeadVariableFree trs 
                                      then abortWith $ text $ "Uncurrying only applicable to applicative, left head variable free TRSs"
                                      else return $ ([newproblem], \ [p] -> UncurryProof p sig vars ucTrs uncurried)
                                          where ((ucTrs,uncurried), sig) = runSignature (uncurry asig (etaSaturate asig trs)) $ F.emptySignature
                                                newproblem = prob{relation=Standard (uncurried `Trs.union` ucTrs), signature=sig}
                                                vars       = Prob.variables prob
       _ -> abortWith $ text "Uncurrying only applicable for standard problems"


-- data UncurryStrategy = UncurryStrategy deriving (Show, Typeable)

-- type instance ProcessorOf UncurryStrategy = Uncurry
-- instance TransformerStrategy UncurryStrategy where
--     transformerStrategyName _   = "uncurry"
--     transformerFlags _          = noFlags
--     transformerDescription _    = ["Uncurrying"]
--     transformerSynopsis _ =  text "uncurry <strategy>"
--     transformerFromFlags _ _ = Uncurry

-- strategy :: Strat
-- strategy = Strat $ TS UncurryStrategy

