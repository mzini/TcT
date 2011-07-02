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
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeOperators #-}

module Tct.Methods 
    (  

    -- * Processors
    -- ** Direct Processors
    success
    -- | this processor returns Yes(?,?)
    , fail
    -- | this processor returns No
    , empty
    -- | this processor returns Yes(1,1) if the strict component is empty      
    , arctic
    -- | this processor implements arctic interpretations
    , matrix
    -- | this processor implements arctic interpretations      
    , bounds
    -- | this processor implements the bounds technique      
    , epostar
    -- | this processor implements exponential path orders      
    , popstar
    -- | this processor implements polynomial path orders            
    , popstarPS
    -- | this processor implements polynomial path orders with parameter substitution      
    , lmpo     
    -- | this processor implements lightweight multiset path orders 
    , lmpoPS
    -- | this processor implements lightweight multiset path orders with parameter substitution            


    -- ** Processor Combinators
    , ite
      -- | @ite g t e@ applies processor @t@ if processor @g@ succeeds, otherwise processor @e@ is applied
    , timeout
      -- > timeout sec t 
      -- aborts processor @t@ after @sec@ seconds
    , before 
      -- | @p1 `before` p2@ first applies processor @p1@, and if that fails processor @p2@      
    , orBetter
      -- | @p1 `orBetter` p2@ applies processor @p1@ and @p2@ in parallel. Returns the 
      --   proof that gives the better certificate
    , orFaster
      -- | @p1 `orFaster` p2@ applies processor @p1@ and @p2@ in parallel. Returns the 
      --   proof of that processor that finishes fastest
    , sequentially
      -- | list version of "before"
    , best
      -- | list version of "orBetter"      
    , fastest
      -- | list version of "orFaster"            
    , upto
    
    -- ** Predicates
    -- | The following predicates return either Yes(?,?) or No
    , isCollapsing
    , isConstructor
    , isDuplicating
    , isLeftLinear
    , isRightLinear
    , isWellFormed
    , isFull
    , isInnermost
    , isOutermost
    , isRCProblem      
    , isDCProblem      
    , isContextSensitive
    -- *** Lifting Haskell functions      
    , trsPredicate
    , problemPredicate
            
      
    -- * Transformations
      -- | This section list all instances of 'Transformation'. A transformation 't' 
      -- is lifted to a 'P.Processor' using the combinator '>>|' or '>>||'.
    , idtrans
      -- | Identity transformation.
    , irr
      -- | On innermost problems, this processor removes inapplicable rules by looking at non-root overlaps.
    , uncurry
      -- | Uncurrying for full and innermost rewriting. Fails for runtime-complexity analysis.
    , weightgap      
      -- | This processor implements the weightgap principle.   
    , Compose.compose
      -- | The 'Transformer' @compose part bound p@ splits the input problem according to 
      -- the 'Partitioning' @part@ into a pair of 'Problem's @(prob1,prob2)@,
      -- constructed according to the second argument @bound@. 
      -- The given 'Processor' @p@ is applied on the first problem @prob1@.
      -- If @p@ succeeds on @prob1@, the input problem is transformed into @prob2@.
      -- 
      -- Let @prob@ denote the input problem, and let 
      -- @w == weakTrs prob@.
      -- Let @(s_1,s_2)@ be the partitioning of @strictTrs prob@ according to the 
      -- 'Partitioning' @part@.
      -- If @bound==Add@, @prob1==prob{strictTrs=s1, weakTrs=s2 `Trs.union` w}$ and 
      -- @prob2==prob{strictTrs=s2, weakTrs=s1 `Trs.union` w}$. The bound on the input problem @prob@
      -- is obtained from the bounds on @prob1@ and @prob2@ by addition. 
      --
      -- If @bound==Mult@, then @prob1@ is as above, 
      -- but @prob2==prob{strictTrs=s2}@. The bound induced on the input problem @prob@
      -- is obtained by multiplication. For @bound==Mult@ this 'Transformer' only
      -- applies to non size-increasing Problems.
      -- If @bound==Compose@, the 'Transformer' behaves as if @bound==Mult@ but 
      -- the non size-increasing restriction is lifted. In this case the bound on the input problem
      -- is obtained by composition.
    , Compose.composeDynamic
      -- | @composeDynamic = compose Dynamic@
      
      -- *** DP Transformations      
    , dependencyPairs
      -- | Implements dependency pair transformation. Only applicable on runtime-complexity problems.
    , dependencyTuples
      -- | Implements dependency tuples transformation. Only applicable on innermost runtime-complexity problems.
    , pathAnalysis
      -- | Implements path analysis. Only applicable on DP-problems as obtained by 'dependencyPairs' or 'dependencyTuples'.
    , usableRules
      -- | Implements path analysis. Only applicable on DP-problems as obtained by 'dependencyPairs' or 'dependencyTuples'.      
    , DPSimp.removeTails
      -- | Removes trailing weak paths and and dangling rules. 
      -- A dependency pair is on a trailing weak path if it is from the weak components and all sucessors in the dependency graph 
      -- are on trailing weak paths. A rule is dangling if it has no successors in the dependency graph.
      --  
      -- Only applicable on DP-problems as obtained by 'dependencyPairs' or 'dependencyTuples'. Also 
      -- not applicable when @strictTrs prob \= Trs.empty@.
    , DPSimp.simpDPRHS      
      -- | Simplifies right-hand sides of dependency pairs. 
      -- Removes r_i from right-hand side @c_n(r_1,...,r_n)@ if no instance of 
      -- r_i can be rewritten.
      --  
      -- Only applicable on DP-problems as obtained by 'dependencyPairs' or 'dependencyTuples'. Also 
      -- not applicable when @strictTrs prob \= Trs.empty@.
      
    -- *** Transformation Combinators     
    , (>>|)    
      -- | The processor @t >>| p@ first applies the transformation @t@. If this succeeds, the processor @p@
      -- is applied on the resulting subproblems. Otherwise @t >>| p@ fails.
    , (>>||)      
      -- | Like '>>|' but resulting subproblems are solved in parallel.
    , try
      -- | The transformer @try t@ behaves like @t@ but succeeds even if @t@ fails. When @t@ fails
      -- the input problem is returned.
    , exhaustively
      -- | The transformer @exhaustively t@ applies @t@ repeatedly until @t@ fails.
    , (>>>)
      -- | The transformer @t1 >>> t2@ first transforms using @t1@, resulting subproblems are 
      -- transformed using @t2@. It succeeds if either @t1@ or @t2@ succeeds.
    , (<>)      
      -- | The transformer @t1 <> t2@ transforms the input using @t1@ if successfull, otherwise
      -- @t2@ is applied.

    -- * Custom Processors
    , processorFromInstance
    , processor 
    , strategy      
    , customInstance
    , CustomProcessor
    , Description(..)
    
      -- ** Arguments
    , Nat (..)
    , nat
    , Size (..)
    , EnumOf
    , Processor
    , NaturalMI.NaturalMIKind (..)
    , Poly.PolyShape(..)
    , Weightgap.WgOn (..)
    , Compose.ComposeBound (..)
    , Compose.Partitioning (..)
    , Approximation(..)
    , Enrichment (..)
    , InitialAutomaton (..)
    , AssocArgument (..)      
    , WhichTrs(..)
    , Assoc 
    , Compose.splitDP
    , Compose.splitRandom
    , Compose.splitSatisfying
    , Compose.splitFirstCongruence      
    , Compose.splitWithoutLeafs
    , P.defaultOptions 
    , MatrixOptions (..)
      
    -- *** Argument Descriptions
    , Arg (..)
    , Unit    
    , (:+:)(..)
    , arg
    , optional
      
    -- *** Argument Description Constructors  
    , assocArg 
    , boolArg
    , enumArg
    , maybeArg
    , naturalArg
    , processorArg

    -- *  Parsable Processors
    , (<|>)
    , AnyProcessor
    , ArcticMI.arcticProcessor
    , bestProcessor
    , boundsProcessor
    , Compose.composeProcessor
    , epostarProcessor
    , failProcessor
    , fastestProcessor
    , iteProcessor
    , lmpoProcessor
    , NaturalMI.matrixProcessor
    , NaturalPI.polyProcessor
    , popstarProcessor
    , sequentiallyProcessor
    , successProcessor
    , timeoutProcessor
    -- ** Predicates
    , isCollapsingProcessor
    , isConstructorProcessor
    , isDuplicatingProcessor
    , isLeftLinearProcessor
    , isRightLinearProcessor
    , isWellFormedProcessor
    , isFullProcessor
    , isInnermostProcessor
    , isOutermostProcessor
    , isContextSensitiveProcessor
      
      -- ** The Built-In Processor Used by TCT
    , builtInProcessors
    , predicateProcessors

    -- ** Transformations
    , irrProcessor    
    , uncurryProcessor
    , dependencyPairsProcessor
    , pathAnalysisProcessor
    , usableRulesProcessor
    , Weightgap.weightgapProcessor
      
      -- ** Misc
    , solveBy
    , withArgs
    )
where
import Prelude hiding (fail, uncurry)
import Control.Monad (liftM)
import Tct.Method.Combinator
import Tct.Method.PopStar
import Tct.Method.EpoStar
import qualified Tct.Method.Compose as Compose
import Tct.Method.Bounds
import qualified Tct.Method.Matrix.ArcticMI as ArcticMI
import qualified Qlogic.ArcSat as ArcSat
import qualified Tct.Method.DP.Simplification as DPSimp
import qualified Tct.Method.Matrix.NaturalMI as NaturalMI
import qualified Tct.Method.Poly.PolynomialInterpretation as Poly
import qualified Tct.Method.Poly.NaturalPI as NaturalPI
import Tct.Method.Custom
import Tct.Method.Predicates
import Tct.Method.Uncurry
import Tct.Method.DP.UsableRules
import Tct.Method.DP.DependencyPairs
import Tct.Method.DP.PathAnalysis
import qualified Tct.Method.Weightgap as Weightgap
import Tct.Method.DP.DependencyGraph
import Tct.Method.InnermostRuleRemoval
import Qlogic.NatSat (Size (..))
import qualified Tct.Processor as P
import qualified Tct.Processor.Standard as S
import Tct.Processor (solveBy)
import Tct.Processor.Standard (withArgs)
import Tct.Processor.Args
import Tct.Processor.Args.Instances
import Tct.Processor.Transformations -- (strict, nonstrict, parallelSubgoals, sequentialSubgoals, TransformationProcessor)
import Tct.Processor.Timeout
import Tct.Processor (none, (<|>), AnyProcessor)

builtInProcessors :: AnyProcessor
builtInProcessors = timeoutProcessor
                   <|> failProcessor 
                   <|> successProcessor
                   <|> iteProcessor
                   <|> irrProcessor
                   <|> bestProcessor
                   <|> fastestProcessor
                   <|> sequentiallyProcessor
                   <|> lmpoProcessor
                   <|> popstarProcessor
                   <|> epostarProcessor
                   <|> boundsProcessor
                   <|> uncurryProcessor
                   <|> usableRulesProcessor
                   <|> DPSimp.removeTailProcessor
                   <|> DPSimp.simpDPRHSProcessor                 
                   <|> dependencyPairsProcessor
                   <|> pathAnalysisProcessor
                   <|> NaturalMI.matrixProcessor
                   <|> NaturalPI.polyProcessor
                   <|> ArcticMI.arcticProcessor
                   <|> Weightgap.weightgapProcessor
                   <|> Compose.composeProcessor
                   <|> emptyProcessor
                   <|> foldr (<|>) none predicateProcessors

-- combinators

-- call :: (P.Processor p) => P.InstanceOf p -> P.InstanceOf P.SomeProcessor
-- call = P.someInstance

upto :: (Enum n, Ord n, P.ComplexityProof (P.ProofOf p), P.Processor p) =>
        (n -> P.InstanceOf p) -> (Bool :+: n :+: n) -> P.InstanceOf (S.StdProcessor (OneOf p))
upto prc (fast :+: l :+: u) | l > u     = fastest []
                            | fast      = fastest subs
                            | otherwise = sequentially subs
    where subs = [ prc i | i <- [l..u] ]

orFaster :: (P.Processor a, P.Processor b) => 
           P.InstanceOf a -> P.InstanceOf b -> P.InstanceOf (S.StdProcessor (OneOf P.SomeProcessor))
a `orFaster` b = fastest [P.someInstance a, P.someInstance b]

orBetter :: (P.Processor a, P.Processor b) => 
           P.InstanceOf a -> P.InstanceOf b -> P.InstanceOf (S.StdProcessor (OneOf P.SomeProcessor))
a `orBetter` b = best [P.someInstance a, P.someInstance b]

before :: (P.Processor a, P.Processor b) => 
           P.InstanceOf a -> P.InstanceOf b -> P.InstanceOf (S.StdProcessor (OneOf P.SomeProcessor))
a `before` b = sequentially [P.someInstance a, P.someInstance b]


-- * defaultMatrix

data MatrixOptions = MatrixOptions { cert :: NaturalMI.NaturalMIKind -- ^ defines how the induced certificate is computed.
                                   , dim  :: Int -- ^ dimension of matrix coefficients. The default is 'Algebraic'.
                                   , degree :: Maybe Int -- ^ upper bound on degree of induced certificate, cf. also cert. The default is @2@.
                                   , bits :: Int -- ^ number of bits used for encoding entries in coefficient matrix. The default is @2@.
                                   , cbits :: Maybe Int -- ^ number of bits used for intermediate results. The default is @Just 3@. If @Nothing@ is given then sizes of intermediate results are not restricted.
                                   , on :: Weightgap.WgOn -- ^ option solely for weightgap
                                   , useUsableArgs :: Bool -- ^ Defines whether monotonicity-constraints are weakened by taking usable argument positions into account. The default is @True@ 
                                   }

instance P.IsDefaultOption MatrixOptions where 
    defaultOptions = MatrixOptions { cert   = NaturalMI.Algebraic
                                   , dim    = 2
                                   , degree = Nothing
                                   , bits   = 2
                                   , cbits  = Just $ 3
                                   , useUsableArgs = True
                                   , on            = Weightgap.WgOnAny }

matrix :: MatrixOptions -> P.InstanceOf (S.StdProcessor NaturalMI.NaturalMI)
matrix m = S.StdProcessor NaturalMI.NaturalMI `S.withArgs` ((cert m) :+: (nat `liftM` degree m) :+: (nat $ dim m) :+: (Nat $ bits m) :+: Nothing :+: (nat `liftM` cbits m) :+: (useUsableArgs m))


arctic :: MatrixOptions -> P.InstanceOf (S.StdProcessor ArcticMI.ArcticMI)
arctic m = S.StdProcessor ArcticMI.ArcticMI `S.withArgs` ((nat $ dim m) :+: (Nat $ ArcSat.intbound $ ArcSat.Bits $ bits m) :+: Nothing :+: (nat `liftM` cbits m) :+: (useUsableArgs m))


weightgap :: MatrixOptions -> TheTransformer Weightgap.WeightGap
weightgap m = Weightgap.WeightGap `calledWith` (on m :+: (cert m) :+: (nat `liftM` degree m) :+: (nat $ dim m) :+: (Nat $ bits m) :+: Nothing :+: (nat `liftM` cbits m) :+: (useUsableArgs m))

-- * defaultPoly

data PolyOptions = PolyOptions { pkind :: Poly.PolyShape
                               , pbits :: Int
                               , pcbits :: Maybe Int
                               , puseUsableArgs :: Bool }

instance P.IsDefaultOption PolyOptions where
  defaultOptions = PolyOptions { pkind          = Poly.Simple
                               , pbits          = 2
                               , pcbits         = Just 3
                               , puseUsableArgs = True }
