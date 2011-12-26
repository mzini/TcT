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
import Termlib.Problem (strictTrs, weakTrs, Strategy (..), Problem (..), StartTerms(..), startTerms)
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

instance P.ComplexityProof PredicateProof where
    answer (PredicateProof _ a) = a
    pprintProof (PredicateProof (TrsPredicate n _) a) _ = text "The input is" <+> ans <+> text n <> text "."
        where ans | P.succeeded a = empty
                  | otherwise     = text "NOT"
    pprintProof (PredicateProof (ProblemPredicate n _) a) _ = text "The input problem is" <+> ans <+> text n <> text "."
        where ans | P.succeeded a = empty
                  | otherwise     = text "NOT"

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
              ans | holds     = P.yesAnswer
                  | otherwise = P.NoAnswer
    arguments _ = opt { A.name = "on"
                      , A.description = unlines [ "Chooses the TRS from the problem on which the predicate is applied (only applies to predicates on TRSs)."]
                      , A.defaultValue = Strict}


type PredicateProcessor = S.StdProcessor Predicate
         
trsPredicateProcessor :: String -> (Trs -> Bool) -> PredicateProcessor     
trsPredicateProcessor s p = S.StdProcessor $ TrsPredicate s p
problemPredicateProcessor :: String -> (Problem -> Bool) -> PredicateProcessor     
problemPredicateProcessor s p = S.StdProcessor $ ProblemPredicate s p


isDuplicatingProcessor :: PredicateProcessor
isDuplicatingProcessor = trsPredicateProcessor "duplicating" Trs.isDuplicating
isConstructorProcessor :: PredicateProcessor
isConstructorProcessor = trsPredicateProcessor "constructor" Trs.isConstructor
isCollapsingProcessor :: PredicateProcessor
isCollapsingProcessor = trsPredicateProcessor "collapsing" Trs.isCollapsing
isGroundProcessor :: PredicateProcessor
isGroundProcessor = trsPredicateProcessor "ground" Trs.isGround
isLeftLinearProcessor :: PredicateProcessor
isLeftLinearProcessor = trsPredicateProcessor "leftlinear" Trs.isLeftLinear
isRightLinearProcessor :: PredicateProcessor
isRightLinearProcessor = trsPredicateProcessor "rightlinear" Trs.isRightLinear
isWellFormedProcessor :: PredicateProcessor
isWellFormedProcessor = trsPredicateProcessor "wellformed" Trs.wellFormed

isStrat :: String -> (Strategy -> Bool) -> PredicateProcessor
isStrat n check = problemPredicateProcessor n (\ prob -> check $ strategy prob)
isStartTerms :: String -> (StartTerms -> Bool) -> PredicateProcessor
isStartTerms n check = problemPredicateProcessor n (\ prob -> check $ startTerms prob)

isOutermostProcessor :: PredicateProcessor
isOutermostProcessor = isStrat "outermost" ((==) Outermost)
isInnermostProcessor :: PredicateProcessor
isInnermostProcessor = isStrat "innermost" ((==) Innermost)
isFullProcessor :: PredicateProcessor
isFullProcessor = isStrat "fullstrategy" ((==) Full)
isContextSensitiveProcessor :: PredicateProcessor
isContextSensitiveProcessor = isStrat "contextsensitive" (\ s -> case s of ContextSensitive _ -> True; _ -> False)
isDCProblemProcessor :: PredicateProcessor
isDCProblemProcessor = isStartTerms "DC problem" ((==) TermAlgebra)
isRCProblemProcessor :: PredicateProcessor
isRCProblemProcessor = isStartTerms "RC problem" (\ t -> case t of BasicTerms{} -> True; _ -> False)

predicateProcessors :: [PredicateProcessor]
predicateProcessors = [ isDuplicatingProcessor
                      , isConstructorProcessor
                      , isCollapsingProcessor
                      , isGroundProcessor
                      , isLeftLinearProcessor
                      , isRightLinearProcessor
                      , isWellFormedProcessor
                      , isOutermostProcessor
                      , isFullProcessor
                      , isInnermostProcessor
                      , isContextSensitiveProcessor ]


trsPredicate :: String -> (Trs -> Bool) -> WhichTrs -> P.InstanceOf (S.StdProcessor Predicate)
trsPredicate s p a = (S.StdProcessor $ TrsPredicate s p) `S.withArgs` a

problemPredicate :: String -> (Problem -> Bool) -> P.InstanceOf (S.StdProcessor Predicate)
problemPredicate s p = (S.StdProcessor $ ProblemPredicate s p) `S.withArgs` Union


isDuplicating :: WhichTrs -> P.InstanceOf (S.StdProcessor Predicate)
isDuplicating a = isDuplicatingProcessor `S.withArgs` a
isCollapsing :: WhichTrs -> P.InstanceOf (S.StdProcessor Predicate)
isCollapsing a = isCollapsingProcessor `S.withArgs` a
isConstructor :: WhichTrs -> P.InstanceOf (S.StdProcessor Predicate)
isConstructor a = isConstructorProcessor `S.withArgs` a
isGround :: WhichTrs -> P.InstanceOf (S.StdProcessor Predicate)
isGround a = isGroundProcessor `S.withArgs` a
isLeftLinear :: WhichTrs -> P.InstanceOf (S.StdProcessor Predicate)
isLeftLinear a = isLeftLinearProcessor `S.withArgs` a
isRightLinear :: WhichTrs -> P.InstanceOf (S.StdProcessor Predicate)
isRightLinear a = isRightLinearProcessor `S.withArgs` a
isWellFormed :: WhichTrs -> P.InstanceOf (S.StdProcessor Predicate)
isWellFormed a = isWellFormedProcessor `S.withArgs` a
isOutermost :: P.InstanceOf (S.StdProcessor Predicate)
isOutermost = isOutermostProcessor `S.withArgs` Union
isInnermost :: P.InstanceOf (S.StdProcessor Predicate)
isInnermost = isInnermostProcessor `S.withArgs` Union
isFull :: P.InstanceOf (S.StdProcessor Predicate)
isFull = isFullProcessor `S.withArgs` Union
isContextSensitive :: P.InstanceOf (S.StdProcessor Predicate)
isContextSensitive = isContextSensitiveProcessor `S.withArgs` Union

isDCProblem :: P.InstanceOf (S.StdProcessor Predicate)
isDCProblem = isDCProblemProcessor `S.withArgs` Union
isRCProblem :: P.InstanceOf (S.StdProcessor Predicate)
isRCProblem = isRCProblemProcessor `S.withArgs` Union

