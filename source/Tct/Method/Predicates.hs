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
import Termlib.Problem (strictTrs, weakTrs, Strategy (..), Problem (..))
import qualified Tct.Processor.Args as A
import Tct.Processor.Args
import Tct.Processor.Args.Instances
import qualified Tct.Processor.Standard as S
import qualified Tct.Processor as P


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


data Predicate = TrsPredicate String (Trs -> Bool)
               | ProblemPredicate String (Problem -> Bool)
data PredicateProof = PredicateProof Predicate P.Answer

instance P.Answerable PredicateProof where
    answer (PredicateProof _ a) = a

instance PrettyPrintable PredicateProof where
    pprint (PredicateProof (TrsPredicate n _) a) = text "The input is" <+> ans <+> text n <> text "."
        where ans | P.succeeded a = empty
                  | otherwise     = text "NOT"
    pprint (PredicateProof (ProblemPredicate n _) a) = text "The input problem is" <+> ans <+> text n <> text "."
        where ans | P.succeeded a = empty
                  | otherwise     = text "NOT"

instance P.Verifiable PredicateProof where
    verify _ _ = P.verifyOK

instance S.Processor Predicate where
    type S.ArgumentsOf Predicate = Arg (EnumOf WhichTrs)
    type S.ProofOf Predicate = PredicateProof
    name (TrsPredicate n _) = n
    name (ProblemPredicate n _) = n
    solve inst prob = return $ PredicateProof proc ans
        where proc = S.processor inst
              holds = case proc of 
                        TrsPredicate _ p -> 
                            case S.processorArgs inst of 
                              Strict -> p $ strictTrs prob
                              Weak   -> p $ weakTrs prob
                              Union  -> p $ strictTrs prob `Trs.union` weakTrs prob
                              Both   -> p (strictTrs prob) &&  p (weakTrs prob)
                        ProblemPredicate _ p -> p prob                              
              ans | holds     = P.YesAnswer
                  | otherwise = P.NoAnswer
    arguments _ = opt { A.name = "on"
                      , A.description = unlines [ "Chooses the TRS from the problem on which the predicate is applied (only applies to predicates on TRSs)."]
                      , A.defaultValue = Strict}


type PredicateProcessor = S.StdProcessor Predicate
         
trsPredicate :: String -> (Trs -> Bool) -> PredicateProcessor     
trsPredicate s p = S.StdProcessor $ TrsPredicate s p

problemPredicate :: String -> (Problem -> Bool) -> PredicateProcessor     
problemPredicate s p = S.StdProcessor $ ProblemPredicate s p


isDuplicating :: PredicateProcessor
isDuplicating = trsPredicate "duplicating" Trs.isDuplicating
isConstructor :: PredicateProcessor
isConstructor = trsPredicate "constructor" Trs.isConstructor
isCollapsing :: PredicateProcessor
isCollapsing = trsPredicate "collapsing" Trs.isCollapsing
isGround :: PredicateProcessor
isGround = trsPredicate "ground" Trs.isGround
isLeftLinear :: PredicateProcessor
isLeftLinear = trsPredicate "leftlinear" Trs.isLeftLinear
isRightLinear :: PredicateProcessor
isRightLinear = trsPredicate "rightlinear" Trs.isLeftLinear
isWellFormed :: PredicateProcessor
isWellFormed = trsPredicate "wellformed" Trs.wellFormed

isStrat :: String -> (Strategy -> Bool) -> PredicateProcessor
isStrat n check = problemPredicate n (\ prob -> check $ strategy prob)

isOutermost :: PredicateProcessor
isOutermost = isStrat "outermost" ((==) Outermost)
isInnermost :: PredicateProcessor
isInnermost = isStrat "innermost" ((==) Innermost)
isFull :: PredicateProcessor
isFull      = isStrat "fullstrategy" ((==) Full)
isContextSensitive :: PredicateProcessor
isContextSensitive = isStrat "contextsensitive" (\ s -> case s of ContextSensitive _ -> True; _ -> False)

predicateProcessors :: [PredicateProcessor]
predicateProcessors = [isDuplicating
                      , isConstructor
                      , isCollapsing
                      , isGround
                      , isLeftLinear
                      , isRightLinear
                      , isWellFormed
                      , isOutermost
                      , isFull
                      , isInnermost
                      , isContextSensitive ]

