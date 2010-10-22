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

{-# LANGUAGE ParallelListComp #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Tct.Encoding.UsablePositions
  -- ( UsablePositions
  -- , empty
  -- )
where

import Termlib.Rule (Rule(..))
import Termlib.Substitution (isRenamedUnifiable)
import Termlib.Term
import Termlib.Trs (Trs(..))
import Termlib.Problem hiding (variables)
import qualified Termlib.Trs as Trs

import qualified Data.IntSet as IntSet
import qualified Data.IntMap as IntMap
import qualified Data.Set as Set
import Data.IntSet (IntSet)
import Data.IntMap (IntMap)
import Data.List (sort, partition)
import Data.Typeable
import Termlib.Utils (PrettyPrintable(..), enum)
import Termlib.FunctionSymbol
import Text.PrettyPrint.HughesPJ hiding (empty)

newtype UsablePositions = UP (IntMap IntSet) deriving (Eq, Show)


empty :: UsablePositions
empty = UP IntMap.empty

singleton :: Symbol -> [Int] -> UsablePositions
singleton sym is = UP $ IntMap.singleton (enum sym) (IntSet.fromList is)

usablePositions :: Symbol -> UsablePositions -> [Int]
usablePositions sym (UP m) = case IntMap.lookup (enum sym) m of 
                               Just poss -> sort $ IntSet.toList $ poss
                               Nothing -> []

setUsable :: Symbol -> Int -> UsablePositions -> UsablePositions
setUsable sym i (UP m) = UP $ IntMap.alter alter (enum sym) m
  where alter (Just s) = Just $ IntSet.insert i s
        alter Nothing = Just $ IntSet.singleton i

setUsables :: Symbol -> [Int] -> UsablePositions -> UsablePositions
setUsables sym is sm = foldl (\ sm' i -> setUsable sym i sm') sm is


union :: UsablePositions -> UsablePositions -> UsablePositions
(UP u1) `union` (UP u2) = UP $ IntMap.unionWith IntSet.union u1 u2

unions :: [UsablePositions] -> UsablePositions
unions = foldl union empty

isUsable :: Symbol -> Int -> UsablePositions -> Bool
isUsable sym i (UP m) = case IntMap.lookup (enum sym) m of 
                          Just poss -> IntSet.member i poss
                          Nothing ->  False

isBlockedProperSubtermOf :: UsablePositions -> Term -> Term -> Bool
isBlockedProperSubtermOf up s t = any (isBlockedProperSubtermOf up s . snd) uSubs || any (isSubtermOf s . snd) nonSubs
  where (uSubs, nonSubs) = partition (\ (i, _) -> isUsable f i up ) $ zip [1 :: Int ..] $ immediateSubterms t
        f                = case root t of
                             Left  _  -> error "Tct.Encoding.UsablePositions.isBlockedProperSubtermOf: root t called for a variable t"
                             Right f' -> f'

instance PrettyPrintable (UsablePositions, Signature) where 
  pprint (up, sig) = fsep $ punctuate (text ",") [ pp sym | sym <- Set.toList $ symbols sig]
    where pp sym = text "Uargs" <> parens (pprint (sym, sig)) <+> text "=" 
                   <+> (braces . fsep . punctuate (text ",") $ [ text $ show i | i <- usablePositions sym up])

data UArgStrategy = UArgByFun | UArgByCap deriving (Typeable, Bounded, Enum)

instance Show UArgStrategy where
  show UArgByFun = "byFunctions"
  show UArgByCap = "byCap"

usableArgs :: UArgStrategy -> Strategy -> Trs -> Trs -> UsablePositions
usableArgs UArgByFun = usableArgsFun
usableArgs UArgByCap = usableArgsCap

usableArgsFun :: Strategy -> Trs -> Trs -> UsablePositions
usableArgsFun Innermost r s = unions [ snd $ uArgs $ rhs rule | rule <- Trs.rules $ Trs.union r s]
    where ds = Trs.definedSymbols s
          uArgs (Var _)    = (False, empty)
          uArgs (Fun f ts) = ( subtermUsable || f `Set.member` ds
                             , unions $ new : [ uargs | (_,_,uargs) <- uArgs'] )
              where uArgs' = [ let (usable,uargs) = uArgs ti in (i,usable,uargs)  | (i, ti) <- zip [1 :: Int ..] ts]
                    subtermUsable = any (\ (_,usable,_) -> usable) uArgs'
                    new = singleton f [i | (i, usable, _) <- uArgs', usable]

usableArgsFun Full r s = foldl (\ up f -> setUsables f (IntSet.toList $ uArgsSym f $ IntSet.empty) up) empty fs 
    where both = r `Trs.union` s
          fs = Set.toList $ Trs.functionSymbols both
          ds = Trs.definedSymbols s

          uArgsSym f us | delta `IntSet.isSubsetOf` us = us
                        | otherwise                    = uArgsSym f (delta `IntSet.union` us)
              where delta   = IntSet.unions [ snd $ uArgs $ rhs rule | rule <- Trs.rules both]

                    rhsVars = Set.unions [ variables li
                                          | rule <- Trs.rules both  -- TODO verify use of both, verify if inlined
                                         , root (lhs rule) == Right f 
                                         , li <- immediateSubterms (lhs rule)]

                    uArgs (Var x)    = (x `Set.member` rhsVars, IntSet.empty)
                    uArgs (Fun g ts) = ( subtermUsable || g `Set.member` ds
                                       , IntSet.unions $ new : [ us' | (_,(_, us')) <- uArgs' ] )
                        where uArgs'          = [ (i, uArgs ti) | (i,ti) <- zip [1 :: Int ..] ts]
                              subtermUsable   = any (\ (_,(isUP,_)) -> isUP) uArgs'
                              new | f == g    = IntSet.fromList [i | (i, (isUp, _)) <- uArgs' , isUp]
                                  | otherwise = IntSet.empty

usableArgsCap :: Strategy -> Trs -> Trs -> UsablePositions
usableArgsCap Innermost r s = usableReplacementMap (r `Trs.union` s) empty
usableArgsCap Full r s = fix (usableReplacementMap $ r `Trs.union` s) empty
    where fix f up | res == up = up
                   | otherwise = fix f (f up)
            where res = f up

usableReplacementMap :: Trs -> UsablePositions -> UsablePositions
usableReplacementMap trs up = unions [ snd $ uArgs l r | Rule l r <- Trs.rules trs]
    where uArgs l t@(Var _)    = ( not $ isBlockedProperSubtermOf up t l, empty)
          uArgs l t@(Fun f ts) = ( not (isBlockedProperSubtermOf up t l) && (subtermUsable || hasRedex)
                             , unions $ new : [ uargs | (_,_,uargs) <- uArgs'] )
              where uArgs' = [ let (usable,uargs) = uArgs l ti in (i,usable,uargs)  | (i, ti) <- zip [1 :: Int ..] ts]
                    subtermUsable = any (\ (_,usable,_) -> usable) uArgs'
                    hasRedex = any (\ rule -> isRenamedUnifiable t $ lhs rule) $ rules trs
                    new = singleton f [i | (i, usable, _) <- uArgs', usable]
