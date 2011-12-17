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
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Tct.Encoding.SafeMapping
  ( SafeMapping
  , SafePosition
  , isSafe
  , isSafeP
  , setSafe
  , setSafes
  , safeArgumentPositions
  , empty
  , validSafeMapping
  )
where

import qualified Data.Map as Map
import qualified Data.IntSet as IntSet
import qualified Data.Set as Set
import Termlib.Rule (Rule(..))
import Termlib.Trs (Trs, rules)
import Termlib.Variable (Variables)
import Termlib.Term
import qualified Termlib.Variable as V

import Data.IntSet (IntSet)
import Data.Typeable
import Qlogic.SatSolver
import Qlogic.Boolean
import Qlogic.PropositionalFormula
import Data.List (sort)
import Termlib.Utils (PrettyPrintable(..))
import Termlib.FunctionSymbol
import Prelude hiding ((||),(&&),not)
import Text.PrettyPrint.HughesPJ hiding (empty)

newtype SafeMapping = SM (Signature, Map.Map Symbol IntSet) deriving Show

newtype SafePosition = SP (Symbol, Int) deriving (Eq, Ord, Typeable, Show)

instance PropAtom SafePosition

empty :: Signature -> Set.Set Symbol -> SafeMapping
empty sig constructors = SM (sig, Map.fromList $ [ (c, IntSet.fromList (argumentPositions sig c))
                                                   | c <- Set.toList constructors] )

isSafe :: SafeMapping -> Symbol -> Int -> Bool
isSafe (SM (_,m)) sym i  = 
  case Map.lookup sym m of 
    Just safePositions -> IntSet.member i safePositions
    Nothing ->  False

safeArgumentPositions :: Symbol -> SafeMapping -> [Int]
safeArgumentPositions sym (SM (_,m)) = case Map.lookup sym m of 
                                         Just safePositions -> sort $ IntSet.toList $ safePositions
                                         Nothing -> []

partitionArguments :: Term -> SafeMapping -> ([Term],[Term])
partitionArguments (Fun f ts) sm = (reverse s, reverse n)
    where sp = safeArgumentPositions f sm
          (s,n) = foldl (\ (s',n') (i,ti) -> if i `elem` sp then (ti:s',n') else (s',ti:n')) ([],[]) (zip [1..] ts) 
partitionArguments _ _ = error "Encoding.SafeMapping.partitionArguments: variable given"

isSafeP :: (Eq l) => Symbol -> Int -> PropFormula l
isSafeP sym i = propAtom $ SP (sym,i)

setSafe :: Symbol -> Int -> SafeMapping -> SafeMapping
setSafe sym i (SM (sig,m)) = SM (sig, Map.alter alter sym m)
  where alter (Just s) = Just $ IntSet.insert i s
        alter Nothing = Just $ IntSet.singleton i

setSafes :: Symbol -> [Int] -> SafeMapping -> SafeMapping
setSafes sym is sm = foldl (\ sm' i -> setSafe sym i sm') sm is


instance Decoder SafeMapping SafePosition where 
  add (SP (f, i)) = setSafe f i

validSafeMapping :: Eq l => [Symbol] -> Signature -> PropFormula l
validSafeMapping constructors sig = bigAnd [ isSafeP con i | con <- constructors, i <- argumentPositions sig con]

instance PrettyPrintable SafeMapping where 
  pprint sm@(SM (sig, _)) = fsep $ punctuate (text ",") [ pp sym | sym <- Set.toList $ symbols sig]
    where pp sym = text "safe" <> parens (pprint (sym, sig)) <+> text "=" 
                   <+> (braces . fsep . punctuate (text ",") $ [ text $ show i | i <- safeArgumentPositions sym sm])


instance PrettyPrintable (Trs, Signature, Variables, SafeMapping) where 
  pprint (trs, sig, var, sm) = braces $ pprs (rules trs) 
      where pprs []          = text ""
            pprs [r]         = ppr r
            pprs rs          = vcat $ [com <+> ppr r | (com,r) <- zip (text " " : repeat (text ",")) rs]

            ppr (Rule l r)   = fsep [ppt l, text "->", ppt r]

            ppt (Var x)      = text $ V.variableName x var
            ppt (Fun f [])   = pprint (f,sig) <> parens ( text "" )
            ppt t@(Fun f _)  = pprint (f,sig) <> parens ( ppa nrm <> text ";" `sa` ppa sf )
                where (sf,nrm) = partitionArguments t sm
                      sa | length sf == 0 = (<>)
                         | otherwise      = (<+>)
            ppa ts           = sep $ punctuate (text ",") [ppt t_i | t_i <- ts]
