{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE CPP #-}

--------------------------------------------------------------------------------
-- | 
-- Module      :  Tct.Instances
-- Copyright   :  (c) Martin Avanzini <martin.avanzini@uibk.ac.at>, 
--                Georg Moser <georg.moser@uibk.ac.at>, 
--                Andreas Schnabl <andreas.schnabl@uibk.ac.at>,
-- License     :  LGPL (see COPYING)
--
-- Maintainer  :  Martin Avanzini <martin.avanzini@uibk.ac.at>
-- Stability   :  unstable
-- Portability :  unportable      
-- 
-- This module reexports direct constructors for /processor instances/
-- of TcT. For description of the corresponding processor, please see module 
-- "Tct.Processors".
-- In addition, this module also exports a wealth of combinators.
--
-- Instances are separated into instances of /standard processors/
-- and instances of /transformations/ for historical reasons. 
-- Whereas standard processors either suceed or fail, transformations
-- construct from a given input problem several subproblems that
-- reflect the complexity of the input problem. 
--------------------------------------------------------------------------------   

module Tct.Instances
    (  
      -- * Standard Processors
      -- | This section collects combinators concerning standard processors, toghether with combinators
      -- on standard processors.
      
      -- ** Trivial Processors      
      Combinators.success
    , Combinators.fail
    , Combinators.open
    , Combinators.empty
      
      
      -- ** Processors Based on Interpretations 
      -- *** Matrix Interpretations
      -- | TcT implements both /matrix interpretations over natural numbers/ and /arctic matrix interpretations/.
    , arctic
    , matrix
      -- | Further customisation of these processors is possible as described in "Tct.Instances#customise"
      
      -- *** Polynomial Interpretations
      -- | TcT implements /polynomial interpretations over natural numbers/.
      -- Configuration parameters are collected in 'PolyOptions', supply 'defaultOptions'
      -- for using plynomial interpretations with default parameters.
    , NaturalPI.poly
    , polys
      -- | The shape of a polynomial influences the computed certificate, 
      -- but has also severe impacts on the time spend on proof search.
      -- In the following, we collect some common shapes of polynomials found
      -- in the literature. Custom shapes can be used with options 'customPolynomial'.
      -- Further customisation of is also possible as described in "Tct.Instances#customise"
    , NaturalPI.simplePolynomial 
    , NaturalPI.linearPolynomial
    , NaturalPI.stronglyLinearPolynomial
    , NaturalPI.simpleMixedPolynomial
    , NaturalPI.quadraticPolynomial
      
      -- **** Custom Polynomial Shapes
    , NaturalPI.customPolynomial
    , Poly.SimpleMonomial
    , (Poly.^^^)
    , Poly.mono
    , Poly.boolCoefficient
    , Poly.constant
      -- *** Customising Interpretations
      -- | #customise# The following classes allow the costumisation of interpretation
      -- techniques implemented in TcT, 
      -- cf., 'arctic', 'matrix' and 'polys' that construct various processors
      -- based on sensible defaults.
      -- To exemplify the usage, 
      -- 
      -- > matrix `withDimension` 3 `withCertBy` Automaton
      -- 
      -- defines an matrix interpretation of dimension @3@, whose complexity certificate
      -- is inferred using automaton techniques. 
    , HasDimension (..)
    , HasCertBy (..)
    , NaturalMI.NaturalMIKind (..)
    , HasDegree (..)
    , HasBits (..)
    , HasCBits (..)
    , HasUsableArgs (..)
    , HasUsableRules (..)
    , HasKind (..)
    , Poly.PolyShape (..)
      -- ** Processors Based on Recursive Path Orderings
#ifdef WithEpoStar
    , EpoStar.epostar
#endif
    , PopStar.popstar
    , PopStar.popstarPS
    , PopStar.lmpo     
    , PopStar.popstarSmall
    , PopStar.popstarSmallPS
    , Mpo.mpo
      
      -- ** Bounds Processor
    , Bounds.bounds
    , Bounds.Automata.Enrichment (..)
    , Bounds.InitialAutomaton (..)
      
     -- ** Control Structures
    , Combinators.ite      
    , Combinators.iteProgress      
    , step
    , upto
    , named
    , bsearch
      
      -- ** Combinators Guiding the Proof Search
    , Combinators.before 
    , Combinators.orBetter
    , Combinators.orFaster
      -- | The following three processors provide list versions of 'before', 'orBetter' and 'orFaster' respectively. 
      -- Note that the type of all given processors need to agree. To mix processors
      -- of different type, use 'some' on the individual arguments. 
    , Combinators.sequentially
    , Combinators.best
    , Combinators.fastest
    
    -- ** Predicates
    -- | The following predicates return either the answer @Yes(?,?)@ or @No@.
    , Predicates.isCollapsing
    , Predicates.isConstructor
    , Predicates.isDuplicating
    , Predicates.isLeftLinear
    , Predicates.isRightLinear
    , Predicates.isWellFormed
    , Predicates.isFull
    , Predicates.isInnermost
    , Predicates.isOutermost
    , Predicates.isRCProblem      
    , Predicates.isDCProblem      
    , Predicates.isContextSensitive
    , Predicates.trsPredicate
    , Predicates.problemPredicate
    , Predicates.WhichTrs(..)
            
      -- * Transformations #MethodsTrans#
      -- | This section list all instances of 'Transformation'. A transformation 't' 
      -- is lifted to a 'P.Processor' using the combinator '>>|' or '>>||'.
      
      -- ** Lifting Transformations to Processors
    , (T.>>|)    
    , (>>!)          
    , (T.>>||)
    , (>>!!)                
      
      -- ** Instances
      -- *** Innermost Rule Removal
    , IRR.irr
      
      -- *** To Innermost Transformation 
    , TOI.toInnermost
      
      -- *** Uncurrying
    , Uncurry.uncurry
      
      -- *** Weightgap Principle
    , weightgap
    , Weightgap.WgOn(..)
    , wgOn
      
      -- *** Decompose
    , Compose.decompose
    , partitionIndependent
    , Compose.decomposeDynamic
    , Compose.decomposeStatic      
    , Compose.greedy      
    , Compose.DecomposeBound (..)
      -- *** Weak Dependency Pairs and Dependency Tuples
    , DP.dependencyPairs
    , DP.dependencyTuples
    , DG.Approximation(..)
      -- *** Path analysis
    , pathAnalysis      
    , linearPathAnalysis
      -- *** Usable Rules
    , UR.usableRules
      -- *** Predecessor Estimation      
    , DPSimp.simpPE
    , DPSimp.simpPEOn
    , DPSimp.withPEOn
      -- *** Dependency Graph Decomposition
    , ComposeRC.decomposeDG
    , ComposeRC.decomposeDGselect
    , ComposeRC.solveUpperWith
    , ComposeRC.solveLowerWith
      -- *** DP Simplifications
    , DPSimp.removeTails
    , DPSimp.removeHeads
    , DPSimp.trivial
    , DPSimp.removeInapplicable  
    , DPSimp.simpDPRHS      
      
    -- ** Combinators     
    -- | Following Combinators work on transformations.
    , TCombinator.try
    , TCombinator.force      
    , (TCombinator.>>>)
    , (TCombinator.<>)      
    , (TCombinator.<||>)            
    , TCombinator.exhaustively
    , te
    , successive      
    , when      
    , TCombinator.idtrans
      

      -- ** Abbreviations
    , toDP
    , dpsimps
    , removeLeaf
    , cleanTail
      
      -- * Inspecting Combinators
    , TimesOut (..)
    , Timed (..)      
    , WithProblem (..)
    , withWDG
    , withCWDG
    , withStrategy
      
      -- * Competition Strategies 
    , rc2011
      -- | Runtime complexity strategy employed in the competition 2011.
    , dc2011
      -- | Derivational complexity strategy employed in the competition 2011.
    , rc2012
      -- | Runtime complexity strategy employed in the competition 2012.
    , dc2012
      -- | Derivational complexity strategy employed in the competition 2012.
    , certify2012
      -- | Strategy for certification employed in the competition 2012.
      
    -- * RuleSelector
    , module Tct.Method.RuleSelector 
      -- * Type Exports
    , S.ProcessorInstance
    , T.TheTransformer
    , EQuantified (..)
    , some 
    )
where
  
import Control.Monad (liftM)
import qualified Tct.Method.Combinator as Combinators
import qualified Tct.Method.PopStar as PopStar
import qualified Tct.Method.Mpo as Mpo
#ifdef WithEpoStar
import qualified Tct.Method.EpoStar as EpoStar
#endif
import qualified Tct.Method.Compose as Compose
import qualified Tct.Method.ComposeRC as ComposeRC
import qualified Tct.Method.Bounds as Bounds
import qualified Tct.Method.Bounds.Automata as Bounds.Automata
import qualified Tct.Method.DP.Simplification as DPSimp
import qualified Tct.Method.Matrix.NaturalMI as NaturalMI
import Tct.Method.Matrix.NaturalMI (matrix)
import Tct.Method.Matrix.ArcticMI (arctic)
import qualified Tct.Method.Poly.PolynomialInterpretation as Poly
import qualified Tct.Method.Poly.NaturalPI as NaturalPI
import qualified Tct.Method.Custom as Custom
import qualified Tct.Method.Predicates as Predicates
import qualified Tct.Method.Uncurry as Uncurry
import qualified Tct.Method.DP.UsableRules as UR
import qualified Tct.Method.DP.DependencyPairs as DP
import qualified Tct.Method.DP.PathAnalysis as PathAnalysis
import qualified Tct.Method.Weightgap as Weightgap
import Tct.Method.Weightgap (weightgap,wgOn)
import qualified Tct.Method.DP.DependencyGraph as DG
import qualified Tct.Method.InnermostRuleRemoval as IRR
import qualified Tct.Method.ToInnermost as TOI
import Tct.Method.RuleSelector
import qualified Tct.Processor as P
import qualified Tct.Processor.Standard as S
import qualified Tct.Method.Timeout as Timeout
import Tct.Processor.Args ((:+:)(..), Unit(..))
import Tct.Processor.Args.Instances (nat)
import Tct.Processor.Transformations ((>>|), (>>||))
import qualified Tct.Processor.Transformations as T
import qualified Tct.Method.TCombinator as TCombinator
import Tct.Method.TCombinator ((>>>),(<>),(<||>),try, force, exhaustively)

import Tct.Method.Combinator (ite, empty, fastest,sequentially)
import Tct.Method.Predicates (WhichTrs (..), isDuplicating)
import qualified Tct.Certificate as Cert

import Termlib.Problem (Problem)
import qualified Termlib.Problem as Prob
import qualified Termlib.Trs as Trs

import qualified Data.List as List

-- | Path Analysis 
pathAnalysis :: T.TheTransformer PathAnalysis.PathAnalysis
pathAnalysis = PathAnalysis.pathAnalysis False

-- | Variation of 'pathAnalysis' that generates only a linear number
-- of sub-problems, in the size of the dependency graph
linearPathAnalysis :: T.TheTransformer PathAnalysis.PathAnalysis
linearPathAnalysis = PathAnalysis.pathAnalysis True

infixr 2 >>!
infixr 2 >>!!

-- | Similar to 'T.>>|' but checks if strict rules are empty
(>>!) :: (P.Processor b, T.Transformer t) =>
         T.TheTransformer t -> P.InstanceOf b -> P.InstanceOf P.SomeProcessor
t >>! p = some $ t >>| (empty `Combinators.before` p )

-- | Similar to 'T.>>||' but checks if strict rules are empty
(>>!!) :: (P.Processor b, T.Transformer t) =>
         T.TheTransformer t -> P.InstanceOf b -> P.InstanceOf P.SomeProcessor
t >>!! p = some $ t >>|| empty `Combinators.before` p 

-- | Transformation 'when b t' applies 't' only when 'b' holds
when :: EQuantified inp (T.TheTransformer T.SomeTransformation) => Bool -> inp -> T.TheTransformer T.SomeTransformation
when b t | b = some t
         | otherwise = some TCombinator.idtrans

-- | List version of '>>>'. 
-- 
-- > successive [t_1..t_n] == t_1 >>> .. >>> t_n

successive :: T.Transformer t => [T.TheTransformer t] -> T.TheTransformer T.SomeTransformation
successive [] = some TCombinator.idtrans
successive [t] = some t
successive (t:ts) = t >>> successive ts


-- | @
-- step [l..u] trans proc
-- @ 
-- successively applies the transformations 
-- @
-- [trans l..trans u]
-- @
-- , additionally checking after each application of @trans i@ 
-- whether @proc i@ can solve the problem. More precise
-- @ 
-- step [l..] trans proc == proc l ``Combinators.before`` (trans l '>>|' (proc l ``Combinators.before`` (trans l '>>|' ...)))
-- @
-- .
-- The resulting processor can be infinite.
step :: (T.Transformer t1, P.Processor a) =>
       [t] -> (t -> T.TheTransformer t1) -> (t -> P.InstanceOf a) -> P.InstanceOf P.SomeProcessor
step []     _ _ = some Combinators.empty
step (i:is) t p = some $ p i `Combinators.before` (t i T.>>| empty `Combinators.before` step is t p)


-- | @
-- upto mkproc (b :+: l :+: u) == f [ mkproc i | i <- [l..u]] 
-- @ 
-- where 
-- @f == fastest@ if @b == True@ and @f == sequentially@ otherwise.
upto :: (Enum n, Ord n, P.ComplexityProof (P.ProofOf p), P.Processor p) =>
        (n -> P.InstanceOf p) -> (Bool :+: n :+: n) -> S.ProcessorInstance (Combinators.OneOf p)
upto prc (fast :+: l :+: u) | l > u     = Combinators.fastest []
                            | fast      = Combinators.fastest subs
                            | otherwise = Combinators.sequentially subs
    where subs = [ prc i | i <- [l..u] ]



bsearch :: (P.Processor proc) => String -> (Maybe Int -> P.InstanceOf proc) -> P.InstanceOf (Custom.Custom Unit (P.ProofOf proc))
bsearch nm mkinst = Custom.Custom { Custom.as = "bsearch-"++nm
                                  , Custom.arguments = Unit 
                                  , Custom.code = \ () -> bsearch' mkinst}
                    `Custom.withArgs` ()
  where bsearch' mk prob = 
          do proof <- P.solve (mk Nothing) prob
             case ub proof of 
               Just 0 -> return proof
               Just n -> search proof 0 (n - 1)
               _      -> return proof
            where search proof l u 
                    | l > u = return proof
                    | otherwise = 
                      do let mean = floor $ fromIntegral (u + l) / (2 :: Double) 
                         proof' <- P.solve (mk $ Just mean) prob
                         case ub proof' of 
                           Just n  -> search proof' l (n - 1)
                           Nothing -> search proof (mean + 1) u
                  ub proof = 
                    case Cert.upperBound $ P.certificate proof of 
                      Cert.Poly b -> b
                      _           -> Nothing


-- | Fast simplifications based on dependency graph analysis.
dpsimps :: T.TheTransformer T.SomeTransformation
dpsimps = some $ force $ 
  try cleanTail
  >>> te DPSimp.removeHeads
  >>> te DPSimp.removeInapplicable
  >>> try DPSimp.simpDPRHS 
  >>> try UR.usableRules
  >>> try DPSimp.trivial
            
-- | use 'DPSimp.simpPEOn' and 'DPSimp.removeTails' to remove leafs from the dependency graph. 
cleanTail :: T.TheTransformer T.SomeTransformation
cleanTail = some $ force $ 
            te (DPSimp.simpPEOn sel)
            >>> te (DPSimp.removeTails >>> try DPSimp.simpDPRHS)
  where 
    sel = selAllOf $ selFromWDG "simple predecessor estimation selector" f
    f wdg = Prob.emptyRuleset { Prob.sdp = Trs.fromRules rs }
      where 
        rs = [ r | (n,(DG.StrictDP, r)) <- DG.lnodes wdg
                 , all isWeak $ DG.lsuccessors wdg n ]
        isWeak (_,(DG.WeakDP,_),_) = True
        isWeak _ = False
        
partitionIndependent :: T.TheTransformer T.SomeTransformation
partitionIndependent = some $ 
  Compose.decomposeStatic (selAllOf selIndependentSG) Compose.Add
  >>> try cleanTail


-- | Tries dependency pairs for RC, and dependency pairs with weightgap, otherwise uses dependency tuples for IRC. 
-- Simpifies the resulting DP problem as much as possible.
toDP :: T.TheTransformer T.SomeTransformation
toDP = 
  try (withStrategy toDP')
  >>> try DPSimp.removeInapplicable
  >>> try cleanTail
  >>> te DPSimp.removeHeads
  >>> te (withStrategy partIndep)
  >>> try cleanTail
  >>> try DPSimp.trivial
  >>> try UR.usableRules
  where 
    toDP' Prob.Innermost = 
      timeout 5 (DP.dependencyPairs >>> try UR.usableRules >>> wgOnUsable)
      <> DP.dependencyTuples
    toDP' _ = DP.dependencyPairs >>> try UR.usableRules >>> try wgOnUsable
    
    partIndep Prob.Innermost = partitionIndependent
    partIndep _ = some $ linearPathAnalysis
    
    wgOnUsable = weightgap `wgOn` Weightgap.WgOnTrs



-- | tries to remove leafs in the congruence graph, 
-- by (i) orienting using predecessor extimation and the given processor, 
-- and (ii) using 'DPSimp.removeTails' and various sensible further simplifications. 
-- Fails only if (i) fails.    
removeLeaf :: P.Processor p => P.InstanceOf p -> T.TheTransformer T.SomeTransformation
removeLeaf p = 
  p `DPSimp.withPEOn` anyStrictLeaf
  >>> try (DPSimp.removeTails >>> try DPSimp.simpDPRHS)
  >>> try UR.usableRules
  >>> try DPSimp.trivial
  where 
    anyStrictLeaf = selAnyOf $ selLeafCWDG `selInter` selStricts
    -- orientAnyStrictLeaf prob 
    --   | innermost = some $ p `DPSimp.withPEOn` anyStrictLeaf
    --   | otherwise = some $ Compose.decompose anyStrictLeaf Compose.Add p
    --   where innermost = Prob.strategy prob == Prob.Innermost 
                               

-- default Options

class HasDimension a where 
  -- | Modify dimesion of method.
  withDimension :: a -> Int -> a
  
class HasCertBy a where 
  -- | Defines under which method a certificate should be obtained
  withCertBy :: a -> NaturalMI.NaturalMIKind -> a
  
class HasDegree a where 
  -- | Specifies an upper bound on the estimated degree, or ounbounded degree if given 'Nothing'.
  withDegree :: a -> Maybe Int -> a
  
class HasBits a where  
  -- | Specifies the number of bits for coefficients.
  withBits :: a -> Int -> a
  
class HasCBits a where  
  -- | Specifies an upper bound on intermediate coefficients, when constructing the interpretation, or unbouneded coefficients if given 'Nothing'
  withCBits :: a -> Maybe Int -> a

class HasUsableArgs a where 
  -- | Specifies that the /usable arguments/ criterion should be employed to weaken monotonicity requirements.
  withUsableArgs :: a -> Bool -> a
  
class HasUsableRules a where 
  -- | Specifies that the /usable rules modulo interpretation/ criterion should be considered.  
  withUsableRules :: a -> Bool -> a

class HasKind a k | a -> k where
  -- | Specify the kind of the interpretation.  
  ofKind :: a -> k -> a
  


-- matrices

instance HasDimension (S.ProcessorInstance NaturalMI.NaturalMI) where
  mx `withDimension` d = S.modifyArguments f mx
    where f (cert :+: deg :+: _ :+: bits :+: bound :+: cbits :+: uargs :+: urules) = 
            (cert :+: deg :+: nat d :+: bits :+: bound :+: cbits :+: uargs :+: urules)
    
instance HasCertBy (S.ProcessorInstance NaturalMI.NaturalMI) where
  mx `withCertBy` c = S.modifyArguments f mx
    where f (_ :+: deg :+: dim :+: bits :+: bound :+: cbits :+: uargs :+: urules) = 
            (c :+: deg :+: dim :+: bits :+: bound :+: cbits :+: uargs :+: urules)
    
instance HasDegree (S.ProcessorInstance NaturalMI.NaturalMI) where
  mx `withDegree` deg = S.modifyArguments f mx
    where f (cert :+: _ :+: dim :+: bits :+: bound :+: cbits :+: uargs :+: urules) = 
            (cert :+: nat `liftM` deg :+: dim :+: bits :+: bound :+: cbits :+: uargs :+: urules)

instance HasBits (S.ProcessorInstance NaturalMI.NaturalMI) where
  mx `withBits` bits = S.modifyArguments f mx
    where f (cert :+: deg :+: dim :+: _        :+: bound :+: cbits :+: uargs :+: urules) = 
            (cert :+: deg :+: dim :+: nat bits :+: bound :+: cbits :+: uargs :+: urules)

instance HasCBits (S.ProcessorInstance NaturalMI.NaturalMI) where
  mx `withCBits` cbits = S.modifyArguments f mx
      where f (cert :+: deg :+: dim :+: bits :+: bound :+: _ :+: uargs :+: urules) = 
              (cert :+: deg :+: dim :+: bits :+: bound :+: nat `liftM` cbits :+: uargs :+: urules)

instance HasUsableArgs (S.ProcessorInstance NaturalMI.NaturalMI) where
  mx `withUsableArgs` uargs = S.modifyArguments f mx
    where f (cert :+: deg :+: dim :+: bits :+: bound :+: cbits :+: _ :+: urules) = 
            (cert :+: deg :+: dim :+: bits :+: bound :+: cbits :+: uargs :+: urules)

instance HasUsableRules (S.ProcessorInstance NaturalMI.NaturalMI) where
  mx `withUsableRules` urules = S.modifyArguments f mx
    where f (cert :+: deg :+: dim :+: bits :+: bound :+: cbits :+: uargs :+: _) = 
            (cert :+: deg :+: dim :+: bits :+: bound :+: cbits :+: uargs :+: urules)

-- weightgap

instance HasDimension (T.TheTransformer Weightgap.WeightGap) where
  wg `withDimension` d = T.modifyArguments f wg
    where f (on :+: rs :+: cert :+: deg :+: _ :+: bits :+: bound :+: cbits :+: uargs :+: urules) = 
            (on :+: rs :+: cert :+: deg :+: nat d :+: bits :+: bound :+: cbits :+: uargs :+: urules)
    
instance HasCertBy (T.TheTransformer Weightgap.WeightGap) where
  wg `withCertBy` c = T.modifyArguments f wg
    where f (on :+: rs :+: _ :+: deg :+: dim :+: bits :+: bound :+: cbits :+: uargs :+: urules) = 
            (on :+: rs :+: c :+: deg :+: dim :+: bits :+: bound :+: cbits :+: uargs :+: urules)
    
instance HasDegree (T.TheTransformer Weightgap.WeightGap) where
  wg `withDegree` deg = T.modifyArguments f wg
    where f (on :+: rs :+: cert :+: _ :+: dim :+: bits :+: bound :+: cbits :+: uargs :+: urules) = 
            (on :+: rs :+: cert :+: nat `liftM` deg :+: dim :+: bits :+: bound :+: cbits :+: uargs :+: urules)

instance HasBits (T.TheTransformer Weightgap.WeightGap) where
  wg `withBits` bits = T.modifyArguments f wg
    where f (on :+: rs :+: cert :+: deg :+: dim :+: _        :+: bound :+: cbits :+: uargs :+: urules) = 
            (on :+: rs :+: cert :+: deg :+: dim :+: nat bits :+: bound :+: cbits :+: uargs :+: urules)

instance HasCBits (T.TheTransformer Weightgap.WeightGap) where
  wg `withCBits` cbits = T.modifyArguments f wg
      where f (on :+: rs :+: cert :+: deg :+: dim :+: bits :+: bound :+: _ :+: uargs :+: urules) = 
              (on :+: rs :+: cert :+: deg :+: dim :+: bits :+: bound :+: nat `liftM` cbits :+: uargs :+: urules)

instance HasUsableArgs (T.TheTransformer Weightgap.WeightGap) where
  wg `withUsableArgs` uargs = T.modifyArguments f wg
    where f (on :+: rs :+: cert :+: deg :+: dim :+: bits :+: bound :+: cbits :+: _ :+: urules) = 
            (on :+: rs :+: cert :+: deg :+: dim :+: bits :+: bound :+: cbits :+: uargs :+: urules)

-- poly


instance HasKind (S.ProcessorInstance NaturalPI.NaturalPI) Poly.PolyShape where
  p `ofKind` k = S.modifyArguments f p 
    where f (_ :+: as) = (k :+: as)

instance HasBits (S.ProcessorInstance NaturalPI.NaturalPI) where
  p `withBits` bits = S.modifyArguments f p 
    where f (k :+: bound :+: _ :+: cbits :+: uargs) = (k :+: bound :+: Just (nat bits) :+: cbits :+: uargs)

instance HasCBits (S.ProcessorInstance NaturalPI.NaturalPI) where
  p `withCBits` cbits = S.modifyArguments f p 
    where f (k :+: bound :+: bits :+: _ :+: uargs) = (k :+: bound :+: bits :+: nat `liftM` cbits :+: uargs)

instance HasUsableArgs (S.ProcessorInstance NaturalPI.NaturalPI) where
  p `withUsableArgs` uargs = S.modifyArguments f p
    where f (k :+: bound :+: bits :+: cbits :+: _) = (k :+: bound :+: bits :+: cbits :+: uargs)  


-- | 'polys n' defines a suitable polynomial of degree 'n'
polys :: Int -> S.ProcessorInstance NaturalPI.NaturalPI
polys 1 = NaturalPI.linearPolynomial
polys n = NaturalPI.customPolynomial inter `withBits` 2 `withCBits` Just 3
  where inter vs = [ Poly.mono [ v Poly.^^^ 1 | v <- vs']
                   | vs' <- List.subsequences vs
                   , length vs' <= n ]
                   ++ [Poly.mono [ v Poly.^^^ 2] | v <- vs] 



-- * Competition Strategies

-- | Shorthand for 'try . exhaustively'
te :: T.Transformer t => T.TheTransformer t -> T.TheTransformer (TCombinator.Try T.SomeTransformation)
te = try . exhaustively

dc2011 :: P.InstanceOf P.SomeProcessor
dc2011 = some $ named "dc2011" $ ite (isDuplicating Strict) Combinators.fail strategy
      where matrices simple c 
              | simple = empty `Combinators.before` fastest [ matrix `withDimension` i `withDegree` Nothing `withCBits` Just 4 `withBits` 3 `withCertBy` c
                                                            | i <- [1..bound] ]
              | otherwise = empty `Combinators.before` fastest [ matrix `withDimension` i `withDegree` Just j `withCBits` Just 4 `withBits` 3 `withCertBy` c
                                                               | (i,j) <- zip [1..bound] [1..]]
            bound       = 6
            direct      = matrices False NaturalMI.Algebraic
            insidewg    = matrices False NaturalMI.Algebraic
            matchbounds = Bounds.bounds Bounds.Minimal Bounds.Match 
                          `Combinators.orFaster` Bounds.bounds Bounds.PerSymbol Bounds.Match
                          
            wgs         = wg `withDimension` 1 `withDegree` Just 1
                          <> wg `withDimension` 2
                          <> wg `withDimension` 3
                          <> wg `withDimension` 4
                          <> wg `withDimension` 5
            wg = weightgap `withCBits` Just 4 `withBits` 3
            strategy    = try IRR.irr 
                          >>| try Uncurry.uncurry 
                          >>| (direct 
                               `Combinators.orFaster` (te wgs >>| insidewg) 
                               `Combinators.orFaster` matchbounds)

rc2011 :: P.InstanceOf P.SomeProcessor
rc2011 = some $ named "rc2011" $ ite Predicates.isInnermost (rc DP.dependencyTuples) (rc DP.dependencyPairs)
    where rc mkdp = try IRR.irr >>| matricesBlockOf 2 `Combinators.orFaster` matchbounds `Combinators.orFaster` dp mkdp
          matricesForDegree deg = [ matrix `withDimension` n `withDegree` Just deg | n <- [deg..if deg > 3 then deg else (deg + 3)]] -- matrices for degree deg
          
          matricesBlockOf l = fastest [ sequentially $ concatMap (\ j -> matricesForDegree (i + (j * l))) [0..] | i <- [1..max 1 l]] 
          -- fastest [ sequentially (matricesForDegree 1 ++ matricesForDegree (1 + l) ++ matricesForDegree (1 + 2l) ...  ] 
          --           , ..., 
          --           sequentially (matricesForDegree l ++ matricesForDegree (l + l) ++ matricesForDegree (l + 2l) ...  ] 
          -- dh l prozesse laufen parallel, und im rad sequentiell
          
          
          matchbounds = Timeout.timeout 5 (Bounds.bounds Bounds.Minimal Bounds.Match 
                                           `Combinators.orFaster` Bounds.bounds Bounds.PerSymbol Bounds.Match)
                        
          dp mkdp = mkdp
                     >>| UR.usableRules 
                     >>| (insideDP 
                         `Combinators.orFaster` (PathAnalysis.pathAnalysis False >>|| UR.usableRules >>| insideDP))
             where insideDP  = te dpsimps' >>| empty `Combinators.before` (try wgUsables >>| te (try dpsimps' >>> wgAll) >>| directs)
                   dpsimps'  = try DPSimp.removeTails 
                               >>> try DPSimp.simpDPRHS 
                               >>> try DPSimp.simpPE                   
                   wgAll     = wg  `withDimension` 1
                               <> wg `withDimension` 2
                               <> wg `withDimension` 3
                   wgUsables = wgUsable `withDimension` 1
                               <> wgUsable `withDimension` 2
                               <> wgUsable `withDimension` 3
                   wg = weightgap `withCBits` Just 4 `withBits` 3
                   wgUsable = wg `wgOn` Weightgap.WgOnTrs
                   
                   directs  = empty `Combinators.before` (matricesBlockOf 3 `Combinators.orFaster` matchbounds)


dc2012 :: P.InstanceOf P.SomeProcessor
dc2012 = 
  named "dc2012" $ 
  ite (isDuplicating Strict) Combinators.fail $
    try IRR.irr
    >>| try Uncurry.uncurry
    >>| dc2012' Combinators.best 
  where dc2012' combinator = 
          combinator [ some empty
                     , some $ timeout 59 $ fastest [matrix `withDimension` i `withDegree` Nothing `withCBits` Just 4 `withBits` 3 `withCertBy` NaturalMI.Algebraic 
                                                   | i <- [1..3] ]
                     , some $ timeout 59 $ bsearch "matrix" (mmx 4)
                     , some $ timeout 59 $ Combinators.iteProgress mxs (dc2012' fastest) empty
                     , some $ timeout 59 $ del >>| dc2012' fastest
                     , some $ timeout 10 matchbounds
                     ]
                      
        matchbounds = Bounds.bounds Bounds.Minimal Bounds.Match 
                      `Combinators.orFaster` Bounds.bounds Bounds.PerSymbol Bounds.Match

        whenNonTrivial t = withProblem $ \ prob ->
          when (not $ Trs.isEmpty $ Prob.strictComponents prob) t

        wg dim deg = weightgap `withCertBy` cert' `withDimension` dim' `withDegree` deg' `withCBits` Just (bits' + 1) `withBits` bits' `wgOn` Weightgap.WgOnAny
          where bits' | dim <= 3 = 3
                      | otherwise = 1
                dim' = max 1 dim
                deg' = if dim' <= deg then Nothing else Just (max 0 deg)                
                cert' | deg' == Just 0 = NaturalMI.Algebraic
                      | otherwise = NaturalMI.Automaton
                     
        mx dim deg = matrix `withCertBy` cert' `withDimension` dim' `withDegree` deg' `withCBits` Just (bits' + 1) `withBits` bits'
          where bits' | dim <= 3 = 3
                      | otherwise = 1
                dim' = max 1 dim
                deg' = if dim' <= deg then Nothing else Just (max 0 deg)
                cert' | deg' == Just 0 = NaturalMI.Algebraic
                      | otherwise = NaturalMI.Automaton

        mmx d Nothing  = mx d d
        mmx d (Just i) = mx d i

        mxs = te (cmp 1) 
              >>> te (cmp 2)
              >>> te (cmp 3) 
              >>> te (cmp 4)
              
        cmp i = whenNonTrivial $ 
                compAdd (mx i i)
                <||> wg i i
                <||> when (i < 4) (compAdd (mx (i + 1) i)
                                   <||> wg (i+1) i)
                <||> when (i < 3) (wg (i+2) 
                                   i <||> compAdd (mx (i + 2) i))

        del = whenNonTrivial $ 
              compMul (mx 2 1) 
              <> compMul (mx 3 2) 
              <> compMul (mx 4 3)
              <> compCom (mx 2 1) 
              <> compCom (mx 3 2) 
              <> compCom (mx 4 3)
                
        compAdd p = Compose.decomposeDynamic Compose.Add p
        compMul p = Compose.greedy $ Compose.decomposeDynamic Compose.Mult p
        compCom p = Compose.greedy $ Compose.decomposeDynamic Compose.Compose p        


rc2012 :: P.InstanceOf P.SomeProcessor
rc2012 = named "rc2012" $ 
          withProblem $ \ prob -> 
           case Prob.strategy prob of 
             Prob.Innermost -> some rc2012RCi
             _ -> some $ Combinators.iteProgress TOI.toInnermost rc2012RCi rc2012RC
    
  where wgOnUsable = wg 2 1 `wgOn` Weightgap.WgOnTrs
          
        matchbounds = Bounds.bounds Bounds.Minimal Bounds.Match 
                      `Combinators.orFaster` Bounds.bounds Bounds.PerSymbol Bounds.Match
                      
        spopstar = PopStar.popstarSmallPS . Just                    

        wg dim deg = weightgap `withCertBy` cert' `withDimension` dim' `withDegree` deg' `withCBits` Just (bits' + 1) `withBits` bits' `wgOn` Weightgap.WgOnAny
          where bits' | dim <= 3 = 3
                      | otherwise = 1
                dim' = max 1 dim
                deg' = if dim' <= deg then Nothing else Just (max 0 deg)                
                cert' | deg' == Just 0 = NaturalMI.Algebraic
                      | otherwise = NaturalMI.Automaton
                     
        mx dim deg = matrix `withCertBy` cert' `withDimension` dim' `withDegree` deg' `withCBits` Just (bits' + 1) `withBits` bits'
          where bits' | dim <= 3 = 3
                      | otherwise = 1
                dim' = max 1 dim
                deg' = if dim' <= deg then Nothing else Just (max 0 deg)
                cert' | deg' == Just 0 = NaturalMI.Algebraic
                      | otherwise = NaturalMI.Automaton
                     
        whenNonTrivial t = withProblem $ \ prob ->
          when (not $ Trs.isEmpty $ Prob.strictComponents prob) t

        isTrivialDP = 
          try DPSimp.removeInapplicable
          >>> try cleanTail 
          >>> try DPSimp.trivial
          >>| empty          

        shiftLeafs = removeLeafs 0 <||> (removeLeafs 1 <> removeLeafs 2)
        
        removeLeafs 0 = exhaustively $ whenNonTrivial $ removeLeaf (mx 1 0)
        removeLeafs i = removeLeaf (spopstar i) 
                        <> (removeLeaf (mx i i) 
                            <||> removeLeaf (mx (i + 1) i)
                            <||> when (i == 1) (removeLeaf (mx 3 1))
                            <||> when (i == 2) (removeLeaf (polys 2)))

        simps = 
          try cleanTail
          >>> try DPSimp.trivial
          >>> try UR.usableRules 

        basics = 
          timeout 5 matchbounds 
          `Combinators.orFaster` PopStar.popstarPS
          `Combinators.orFaster` (te (Compose.decomposeDynamic Compose.Add (polys 3)
                                      <||> Compose.decomposeDynamic Compose.Add (mx 3 3)
                                      <||> Compose.decomposeDynamic Compose.Add (mx 4 3)                        
                                      <||> Compose.decomposeDynamic Compose.Add (mx 4 4)) 
                                  >>! PopStar.popstarPS)

        directs = timeout 58 (te (compse 1) >>> te (compse 2) >>> te (compse 3) >>> te (compse 4) >>| empty)
                  `Combinators.orBetter` timeout 5 matchbounds
                  `Combinators.orBetter` timeout 58 ( bsearch "popstar" PopStar.popstarSmallPS )
                  `Combinators.orBetter` timeout 58 PopStar.popstarPS
          
          where compse i = withProblem $ \ prob ->
                  when (not $ Trs.isEmpty $ Prob.strictComponents prob) $ 
                    Compose.decomposeDynamic Compose.Add (spopstar i) -- binary search auf grad
                    <> (when (i == 2 || i == 3) (Compose.decomposeDynamic Compose.Add (polys i))
                        <||> wg i i
                        <||> Compose.decomposeDynamic Compose.Add (mx i i)
                        <||> when (i < 4) (Compose.decomposeDynamic Compose.Add (mx (i + 1) i)))
          
        rc2012RC = 
          Combinators.best [ some $ timeout 58 $ DP.dependencyPairs >>| isTrivialDP
                           , some $ directs 
                           , some $ Timeout.timeout 58 (dp >>| withProblem (rc2012DP 1))]
          where dp = DP.dependencyPairs 
                     >>> try UR.usableRules 
                     >>> try wgOnUsable
                     
        rc2012RCi = 
          try IRR.irr 
          >>! Combinators.best [ some $ directs 
                               , some $ timeout 58 $ rc2012DPi]
          
        rc2012DP i prob
          | Trs.isEmpty (Prob.strictTrs prob) = some $ rc2012DPi
          | otherwise = some $ 
                        te ( whenNonTrivial $ 
                             when (i == 2 || i == 3) (cmp (polys i))
                             <||> cmp (mx i i)
                             <||> wg i i
                             <||> when (i < 4) (cmp (mx (i+1) i) <||> wg (i + 1) i))
                        >>| withProblem (rc2012DP (i + 1))
                       
          where cmp p = Compose.decompose selStrictRule Compose.Add p
                selStrictRule = selAnyOf (selStricts `selInter` selRules)

        rc2012DPi = 
          toDP >>!! te (withCWDG trans) >>! basics
          where trans cwdg 
                  | cwdgDepth cwdg == (0::Int) = some $ shiftLeafs 
                  | otherwise = some $ timeout 15 shiftLeafs <> removeFirstCongruence
                removeFirstCongruence = 
                  ComposeRC.decomposeDG ComposeRC.decomposeDGselect `ComposeRC.solveUpperWith` proc >>> try simps
                  where proc = try simps >>> te shiftLeafs >>! basics
                cwdgDepth cwdg = maximum $ 0 : [ dp r | r <- DG.roots cwdg]
                  where dp n = maximum $ 0 : [ 1 + dp m | m <- DG.successors cwdg n]

                     

certify2012 :: P.InstanceOf P.SomeProcessor
certify2012 = some $ try IRR.irr >>| step [1..] (te . t) (const empty)
  where t d = some $ Compose.decomposeDynamic Compose.Add (vmx d)
                     -- <> decomposeDynamic Add (vps d)
        vmx dimension = matrix 
                        `withCertBy` NaturalMI.Triangular 
                        `withDimension` dimension
                        `withDegree` Nothing 
                        `withCBits` Just (bits' + 1) 
                        `withBits` bits' 
                        `withUsableArgs` False 
                        `withUsableRules` False
          where bits' | dimension <= 2 = 3
                      | dimension <= 4 = 2
                      | otherwise = 1


-- * existential quantification 

-- | This class establishes a mapping between types and their existential 
-- quantified counterparts.
class EQuantified inp outp | inp -> outp where 
    equantify :: inp -> outp

instance T.Transformer t => EQuantified (T.TheTransformer t) (T.TheTransformer T.SomeTransformation) where
    equantify t = T.someTransformation t

instance P.Processor p => EQuantified (P.InstanceOf p) (P.InstanceOf P.SomeProcessor) where
    equantify p = P.someInstance p

-- | Wrap an object by existential quantification.
some :: EQuantified inp outp => inp -> outp
some = equantify

-- * Operations that work on processors and transformations
-- ** timeout

class TimesOut inp outp | inp -> outp where
  -- | Lifts a processor or transformation to one that times out after given number of seconds
  timeout :: Int -> inp -> outp 
  
instance (P.Processor p, outp ~ S.ProcessorInstance (Timeout.Timeout p)) => TimesOut (P.InstanceOf p) outp  where
  timeout = Timeout.timeout

instance T.Transformer t => TimesOut (T.TheTransformer t) (T.TheTransformer (TCombinator.Timeout t)) where
  timeout = TCombinator.timeout

-- ** timeout

class Timed inp outp | inp -> outp where
  -- | Additionally present timing information
  timed :: inp -> outp 
  
instance (P.Processor p, outp ~ S.ProcessorInstance (Combinators.Timed p)) => Timed (P.InstanceOf p) outp  where
  timed = Combinators.timed

instance T.Transformer t => Timed (T.TheTransformer t) (T.TheTransformer (TCombinator.Timed t)) where
  timed = TCombinator.timed

-- ** With Problem

class WithProblem inp outp | inp -> outp where
   withProblem :: (Problem -> inp) -> outp
   
instance T.Transformer t => WithProblem (T.TheTransformer t) (T.TheTransformer (TCombinator.WithProblem t)) where
  withProblem = TCombinator.withProblem

instance (P.Processor proc, P.ProofOf proc ~ res) => WithProblem (P.InstanceOf proc) (P.InstanceOf (Custom.Custom Unit res)) where
   withProblem f = proc `Custom.withArgs` ()
     where proc = Custom.Custom { Custom.as = "Inspecting Problem..."
                                , Custom.arguments = Unit
                                , Custom.code = \ () prob -> P.solve (f prob) prob}

withStrategy :: WithProblem inp outp => (Prob.Strategy -> inp) -> outp
withStrategy f = withProblem $ \ prob -> f (Prob.strategy prob)

withWDG :: WithProblem inp outp => (DG.DG -> inp) -> outp
withWDG f = withProblem $ \ prob -> f (DG.estimatedDependencyGraph DG.defaultApproximation prob)

withCWDG :: WithProblem inp outp => (DG.CDG -> inp) -> outp
withCWDG f = withProblem $ \ prob -> f (DG.toCongruenceGraph $ DG.estimatedDependencyGraph DG.defaultApproximation prob)


-- * Named

-- | 'named name proc' acts like 'proc', but displays itself under the name 'name' in proof outputs      
named :: P.Processor proc => String -> P.InstanceOf proc -> P.InstanceOf P.SomeProcessor
named n inst = some $ proc `Custom.withArgs` ()
  where proc = Custom.Custom { Custom.as = n
                             , Custom.arguments = Unit 
                             , Custom.code = \ () -> P.solve inst }

               
