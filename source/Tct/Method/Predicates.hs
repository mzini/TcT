{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DeriveDataTypeable #-}
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

module Tct.Method.Predicates where

import Text.PrettyPrint.HughesPJ
import Data.Typeable 
import qualified Termlib.Trs as Trs
import Termlib.Trs (Trs)
import Termlib.Utils (PrettyPrintable (..))
import Termlib.Problem (strictTrs, weakTrs)
import Tct.Proof
import qualified Tct.Processor.Args as A
import Tct.Processor.Args
import Tct.Processor.Args.Instances
import qualified Tct.Processor.Standard as S


data WhichTrs = Strict
              | Weak
              | Both 
              | Union deriving (Typeable, Eq, Ord, Enum, Bounded)

instance Show WhichTrs where
    show Strict = "strict"
    show Weak = "weak"
    show Both = "both"
    show Union = "union"

whichTrs :: Arg (EnumOf WhichTrs)
whichTrs = arg


data Predicate = Predicate String (Trs -> Bool)
data PredicateProof = PredicateProof String Answer

instance Answerable PredicateProof where
    answer (PredicateProof _ a) = a

instance PrettyPrintable PredicateProof where
    pprint (PredicateProof n a) = text "The input is" <+> ans <+> text n <> text "."
        where ans | succeeded a = empty
                  | otherwise   = text "NOT"

instance ComplexityProof PredicateProof

instance S.StdProcessor Predicate where
    type S.ArgumentsOf Predicate = Arg (EnumOf WhichTrs)
    type S.ProofOf Predicate = PredicateProof
    name (Predicate n _) = n
    solve inst prob = return $ PredicateProof n ans
        where Predicate n p = S.processor inst
              holds = case S.processorArgs inst of 
                        Strict -> p $ strictTrs prob
                        Weak   -> p $ weakTrs prob
                        Union  -> p $ strictTrs prob `Trs.union` weakTrs prob
                        Both   -> p (strictTrs prob) &&  p (weakTrs prob)
              ans | holds     = YesAnswer
                  | otherwise = NoAnswer
    arguments _ = opt { A.name = "on"
                      , A.description = unlines [ "Chooses the TRS from the problem on which the predicate is applied,"]
                      , A.defaultValue = Strict}
              

isDuplicating :: Predicate
isDuplicating = Predicate "duplicating" Trs.isDuplicating
isConstructor :: Predicate
isConstructor = Predicate "constructor" Trs.isDuplicating
isCollapsing :: Predicate
isCollapsing = Predicate "collapsing" Trs.isCollapsing
isGround :: Predicate
isGround = Predicate "ground" Trs.isGround
isLeftLinear :: Predicate
isLeftLinear = Predicate "leftlinear" Trs.isLeftLinear
isRightLinear :: Predicate
isRightLinear = Predicate "rightlinear" Trs.isLeftLinear
isWellFormed :: Predicate
isWellFormed = Predicate "wellformed" Trs.wellFormed

predicateProcessors :: [S.Processor Predicate]
predicateProcessors = [S.Processor p 
                       | p <- [ isDuplicating
                              , isConstructor
                              , isCollapsing
                              , isGround
                              , isLeftLinear
                              , isRightLinear
                              , isWellFormed]]

