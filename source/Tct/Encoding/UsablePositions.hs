{- | 
Module      :  Tct.Encoding.UsablePositions
Copyright   :  (c) Martin Avanzini <martin.avanzini@uibk.ac.at>, 
               Georg Moser <georg.moser@uibk.ac.at>, 
               Andreas Schnabl <andreas.schnabl@uibk.ac.at>
License     :  LGPL (see COPYING)

Maintainer  :  Martin Avanzini <martin.avanzini@uibk.ac.at>
Stability   :  unstable
Portability :  unportable      

This module implements usable argument positions.
By convention, n-ary function symbols admit argument positions '[1..n]'.
-}

{-# OPTIONS_HADDOCK prune #-}
{-# LANGUAGE ParallelListComp #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Tct.Encoding.UsablePositions
  ( 
    -- * Usable Argument Positions
    UsablePositions
    -- ** Construction
  , empty
  , singleton
  , usableArgs    
    -- ** Modification
  , setUsable
  , setUsables
  , union
  , unions
    -- ** Querying
  , isUsable
  , usablePositions
  , usableSubtermsOf
    
    -- Unexported
  , emptyWithSignature
  , fullWithSignature
  , restrictToSignature
  , usableArgsWhereApplicable
  , toXml
  )
where

import Termlib.Rule (Rule(..))
import Termlib.Substitution (isRenamedUnifiable)
import Termlib.Term
import Termlib.Trs (Trs)
import Termlib.Problem hiding (variables)
import qualified Termlib.Trs as Trs
import qualified Termlib.FunctionSymbol as F
import Prelude hiding (lookup)
import qualified Data.IntSet as IntSet
import qualified Data.IntMap as IntMap
import qualified Data.Set as Set
import Data.IntSet (IntSet)
import Data.IntMap (IntMap)
import Data.List (sort, partition)
import Data.Typeable
import Termlib.Utils (PrettyPrintable(..), enum, invEnum)
import Termlib.FunctionSymbol
import Text.PrettyPrint.HughesPJ hiding (empty)
import qualified Tct.Utils.Xml as Xml


newtype UsablePositions = UP (IntMap IntSet) deriving (Eq, Show)

toXml :: Signature -> UsablePositions -> Xml.XmlContent
toXml sig (UP m) = 
  Xml.elt "usablePositions" []
    [ Xml.elt "usable" [] $
       [ Xml.elt "name" [] [Xml.text $ F.symbolName sig $ invEnum f]
       , Xml.elt "arity" [] [Xml.int $ F.arity sig $ invEnum f] ] 
       ++ [ Xml.elt "position" [] [Xml.int i] | i <- IntSet.toList is]  
    | (f,is) <- IntMap.toList m]


-- | Empty usable positions.
empty :: UsablePositions
empty = UP IntMap.empty

-- | Constructs usable argument for a single function symbol.
singleton :: Symbol -> [Int] -> UsablePositions
singleton sym is = UP $ IntMap.singleton (enum sym) (IntSet.fromList is)


-- | Returns the list of usable argument positions.
usablePositions :: Symbol -> UsablePositions -> [Int]
usablePositions sym (UP m) = case IntMap.lookup (enum sym) m of 
                               Just poss -> sort $ IntSet.toList $ poss
                               Nothing -> []


-- | Sets the ith argument position of given symbol usable.
setUsable :: Symbol -> Int -> UsablePositions -> UsablePositions
setUsable sym i (UP m) = UP $ IntMap.alter alter (enum sym) m
  where alter (Just s) = Just $ IntSet.insert i s
        alter Nothing = Just $ IntSet.singleton i

-- | List version of 'setUsable'.
setUsables :: Symbol -> [Int] -> UsablePositions -> UsablePositions
setUsables sym is sm = foldl (\ sm' i -> setUsable sym i sm') sm is


-- | Union on usable argument positions.
union :: UsablePositions -> UsablePositions -> UsablePositions
(UP u1) `union` (UP u2) = UP $ IntMap.unionWith IntSet.union u1 u2

-- | List version of 'union'.
unions :: [UsablePositions] -> UsablePositions
unions = foldl union empty

emptyWithSignature :: Signature -> UsablePositions
emptyWithSignature sig = unions $ map (\ f -> singleton f []) $ Set.toList $ symbols sig

fullWithSignature :: Signature -> UsablePositions
fullWithSignature sig = unions $ map (\ f -> singleton f $ argumentPositions sig f) $ Set.toList $ symbols sig

restrictToSignature :: Signature -> UsablePositions -> UsablePositions
restrictToSignature sig (UP ua) = UP $ IntMap.filterWithKey (\f _ -> invEnum f `lookup` sig /= Nothing) ua

-- | Predicate that returns true iff the ith argument position is usable.
isUsable :: Symbol -> Int -> UsablePositions -> Bool
isUsable sym i (UP m) = case IntMap.lookup (enum sym) m of 
                          Just poss -> IntSet.member i poss
                          Nothing ->  False

-- | Returns the list of subterms under usable positions of a given term.
usableSubtermsOf :: UsablePositions -> Term -> [Term]
usableSubtermsOf _   v@(Var _)   = [v]
usableSubtermsOf up t@(Fun f ts) = t : usables ++ concatMap (usableSubtermsOf up) usables
    where usables = [ ti | (i,ti) <- zip [1..] ts, isUsable f i up ]



instance PrettyPrintable (UsablePositions, Signature) where 
  pprint (up, sig) 
      | null syms = text "none" 
      | otherwise = fsep $ punctuate (text ",") [ pp sym | sym <- syms]
    where pp sym = text "Uargs" <> parens (pprint (sym, sig)) <+> text "=" 
                   <+> (braces . fsep . punctuate (text ",") $ [ text $ show i | i <- usablePositions sym up])
          syms = Set.toList $ Set.filter (\sym -> arity sig sym > 0 && not (null $ usablePositions sym up) ) $ symbols sig
data UArgStrategy = UArgByFun | UArgByCap deriving (Typeable, Bounded, Enum)

instance Show UArgStrategy where
  show UArgByFun = "byFunctions"
  show UArgByCap = "byCap"

-- | Constructs the usable argument positions of a given TRS, 
-- with respect to a given strategy.
usableArgs :: Strategy -> Trs -> UsablePositions
usableArgs = usableArgsCap

usableArgsCap :: Strategy -> Trs -> UsablePositions
usableArgsCap Innermost r = usableReplacementMap r empty
usableArgsCap _ r         = fix (usableReplacementMap  r) empty
    where fix f up | res == up = up
                   | otherwise = fix f res
            where res = f up

usableReplacementMap :: Trs -> UsablePositions -> UsablePositions
usableReplacementMap trs up = unions [ snd $ uArgs l r | Rule l r <- Trs.rules trs]
    where uArgs l t@(Var _)    = ( not $ isBlockedProperSubtermOf t l, empty)
          uArgs l t@(Fun f ts) = ( not (isBlockedProperSubtermOf t l) && (subtermUsable || hasRedex)
                             , unions $ new : [ uargs | (_,_,uargs) <- uArgs'] )
              where uArgs' = [ let (usable,uargs) = uArgs l ti in (i,usable,uargs)  | (i, ti) <- zip [1 :: Int ..] ts]
                    subtermUsable = any (\ (_,usable,_) -> usable) uArgs'
                    hasRedex = any (\ rule -> isRenamedUnifiable t $ lhs rule) $ Trs.rules trs
                    new = singleton f [i | (i, usable, _) <- uArgs', usable]
          isBlockedProperSubtermOf s t = any (isBlockedProperSubtermOf s . snd) uSubs || any (isSubtermOf s . snd) nonSubs
              where (uSubs, nonSubs) = partition (\ (i, _) -> isUsable f i up ) $ zip [1 :: Int ..] $ immediateSubterms t
                    f                = case root t of
                                         Left  _  -> error "Tct.Encoding.UsablePositions.isBlockedProperSubtermOf: root t called for a variable t"
                                         Right f' -> f'

usableArgsWhereApplicable :: Bool -> F.Signature -> StartTerms -> Bool -> Strategy -> Trs.Trs -> UsablePositions
usableArgsWhereApplicable True sig _ ua strat r = ua' `union` emptyWithSignature nonCompSig
  where ua' | ua = restrictToSignature compSig (usableArgs strat r) 
            | otherwise = fullWithSignature compSig
        compSig    = F.restrictToSymbols sig $ Set.filter (F.isCompound sig) $ F.symbols sig
        nonCompSig = F.restrictToSymbols sig $ Set.filter (not . F.isCompound sig) $ F.symbols sig
usableArgsWhereApplicable _ sig TermAlgebra {} _  _ _ = fullWithSignature sig
usableArgsWhereApplicable _ sig BasicTerms {} ua strat r = if ua then usableArgs strat r else fullWithSignature sig
