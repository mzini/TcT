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
-- and instances of /transformations/ for historical reasons. The instance type of a standard processor @p@ is
-- @'P.InstanceOf' ('S.StdProcessor' p)@, for thransformation @t@ the instance 
-- type is @'T.TheTransformer' t@. 
--------------------------------------------------------------------------------   

{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeFamilies #-}
{-# OPTIONS_HADDOCK not-home #-}
module Tct.Instances
    (  

    -- * Standard Processors
    -- | This section collects combinators concerning standard processors, toghether with combinators
    -- on standard processors.
    Combinators.success
    -- | This processor returns 'Yes(?,?)'.
    , Combinators.fail
    -- | This processor returns 'No'.
    , Combinators.empty
    -- | This processor returns 'Yes(O(1),(1))' if the strict component is empty.
    , Combinators.open
    -- | This processor returns 'Maybe'
    , arctic
    -- | This processor implements arctic interpretations.
    , matrix
    -- | This processor implements matrix interpretations.     
    , poly
    -- | This processor implements polynomial path orders.
    , Bounds.bounds
    -- | This processor implements the bounds technique.
    , EpoStar.epostar
    -- | This processor implements exponential path orders.
    , PopStar.popstar
    -- | This processor implements polynomial path orders.
    , PopStar.popstarPS
    -- | This processor implements polynomial path orders with parameter substitution.
    , PopStar.lmpo     
    -- | This processor implements lightweight multiset path orders.
    , PopStar.popstarSmall
    -- | This processor implements small polynomial path orders (polynomial path orders with product extension and weak safe composition) 
    --   which allow to determine the degree of the obtained polynomial certificate.
    , PopStar.popstarSmallPS
    -- | This processor implements small polynomial path orders (polynomial path orders with product extension and weak safe composition) 
    --   with parameter substitution which allow to determine the degree of the obtained polynomial certificate.
    , rc2011
    -- | This processor reflects the runtime complexity strategy employed in the competition 2011.
    , dc2011
    -- | This processor reflects the derivational complexity strategy employed in the competition 2011.
    
     -- ** Combinators
    , Combinators.ite
      -- | @ite g t e@ applies processor @t@ if processor @g@ succeeds, otherwise processor @e@ is applied.
    , Timeout.timeout
      -- | @timeout sec t@ 
      -- aborts processor @t@ after @sec@ seconds.
    , before 
      -- | @p1 `before` p2@ first applies processor @p1@, and if that fails processor @p2@.
    , orBetter
      -- | @p1 `orBetter` p2@ applies processor @p1@ and @p2@ in parallel. Returns the 
      --   proof that gives the better certificate.
    , orFaster
      -- | @p1 `orFaster` p2@ applies processor @p1@ and @p2@ in parallel. Returns the 
      --   proof of that processor that finishes fastest.
    , Combinators.sequentially
      -- | list version of 'before'. 
      -- Note that the type of all given processors need to agree. To mix processors
      -- of different type, use 'some' on the individual arguments. 
    , Combinators.best
      -- | list version of 'orBetter'.
      -- Note that the type of all given processors need to agree. To mix processors
      -- of different type, use 'some' on the individual arguments. 
    , Combinators.fastest
      -- | list version of 'orFaster'.
      -- Note that the type of all given processors need to agree. To mix processors
      -- of different type, use 'some' on the individual arguments. 
    , withProblem
    -- | The instance @withProblem mkproc@ allows the creation of a processor 
      -- depending on the problem it should handle.
    , step
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
      -- step [l..] trans proc == proc l `before` (trans l >>| (proc l `before` (trans l >>| ...)))
      -- @
      -- .
      -- The resulting processor can be infinite.

    , upto
      -- | @
      -- upto mkproc (b :+: l :+: u) == f [ mkproc i | i <- [l..u]] 
      -- @ 
      -- where 
      -- @f == fastest@ if @b == True@ and @f == sequentially@ otherwise.
    
    -- ** Predicates
    -- | The following predicates return either Yes(?,?) or No.
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
      
    -- * Transformations #MethodsTrans#
      -- | This section list all instances of 'Transformation'. A transformation 't' 
      -- is lifted to a 'P.Processor' using the combinator '>>|' or '>>||'.
    , T.idtrans
      -- | Identity transformation.
    , IRR.irr
      -- | On innermost problems, this processor removes inapplicable rules by looking at non-root overlaps.
    , Uncurry.uncurry
      -- | Uncurrying for full and innermost rewriting. Fails for runtime-complexity analysis.
    , weightgap      
      -- | This processor implements the weightgap principle.   
    , Compose.compose
      -- | This transformation implements techniques for splitting the complexity problem
      -- into two complexity problems (A) and (B) so that the complexity of the input problem
      -- can be estimated by the complexity of the transformed problem. 
      -- The processor closely follows the ideas presented in
      -- /Complexity Bounds From Relative Termination Proofs/
      -- (<http://www.imn.htwk-leipzig.de/~waldmann/talk/06/rpt/rel/main.pdf>).
    , Compose.composeDynamic
      -- | @composeDynamic = compose Dynamic@.
    , Compose.composeStatic
      -- | @composeStatic rs = compose (Static rs)@.
      
      -- *** DP Transformations      
      -- | The following transformations operate only on (weak) dependency pair problems.
    , DP.dependencyPairs
      -- | Implements dependency pair transformation. Only applicable on runtime-complexity problems.
    , DP.dependencyTuples
      -- | Implements dependency tuples transformation. Only applicable on innermost runtime-complexity problems.
    , PathAnalysis.pathAnalysis
      -- | Implements path analysis. Only applicable on DP-problems as obtained by 'dependencyPairs' or 'dependencyTuples'.
    , UR.usableRules
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
    , DPSimp.simpKP
      -- | Knowledge Propagation. 
    , ComposeRC.composeRC
      -- | A compose processor specific for RC.
    , ComposeRC.solveAWith
      -- | Specify a processor to solve Problem A immediately. 
      -- The Transformation aborts if the problem cannot be handled.
    , ComposeRC.solveBWith
      -- | Specify a processor to solve Problem B immediately. 
      -- The Transformation aborts if the problem cannot be handled.
    , dpsimps
      -- | fast simplifications based on dependency graph analysis
      
    -- *** Combinators     
    , (T.>>|)    
      -- | The processor @t >>| p@ first applies the transformation @t@. If this succeeds, the processor @p@
      -- is applied on the resulting subproblems. Otherwise @t >>| p@ fails.
    , (T.>>||)      
      -- | Like '>>|' but resulting subproblems are solved in parallel.
    , T.try
      -- | The transformer @try t@ behaves like @t@ but succeeds even if @t@ fails. When @t@ fails
      -- the input problem is returned.
    , exhaustively
      -- | The transformer @exhaustively t@ applies @t@ repeatedly until @t@ fails.
    , (T.>>>)
      -- | The transformer @t1 >>> t2@ first transforms using @t1@, resulting subproblems are 
      -- transformed using @t2@. It succeeds if either @t1@ or @t2@ succeeds.
    , (T.<>)      
      -- | The transformer @t1 <> t2@ transforms the input using @t1@ if successfull, otherwise
      -- @t2@ is applied.

    -- ** Custom Processors
    , Custom.named
      -- | 'named name proc' acts like 'proc', but displays itself under the name 'name' in proof outputs      
    , Custom.processorFromInstance
      -- | 'processorFromInstance mkproc d' yields a new processor with name and arguments according to description 'd'. 
      -- Here 'd' is usually of type @'Custom.Description' args@, where 'args' is an
      -- instance of 'Args.ParsableArguments'.
      -- See "Tct.Methods#argdescr" for a list of built-in arguments. 
      -- More complex arguments can be build using 'arg' and 'optional', tupling is performed using 'Args.:+:', 
      -- the empty argument list is constructed with 'Args.Unit'.
      -- The processor applies the instance 'mkproc as' to the input problem, where 'as' are the parsed arguments. 
      
    , Custom.strategy      
      -- | this function acts like 'Custom.processorFromInstance', except that the resulting proof 
      -- is wraped into a 'P.SomeProof'.
    , Custom.processor 
    , Custom.customInstance
      
    , Custom.IsDescription(..)      
    , Custom.CustomProcessor
    , Custom.Description(..)
    
      -- ** Arguments
    , Size (..)
    , NaturalMI.NaturalMIKind (..)
    , Weightgap.WgOn (..)
    , Compose.ComposeBound (..)
    , Compose.Partitioning (..)
    , DG.Approximation(..)
    , Bounds.Enrichment (..)
    , Bounds.InitialAutomaton (..)
    , Predicates.WhichTrs(..)
    -- *** RuleSelector
    -- | A @RuleSelector@ is used to select 
    -- rules from a problem. Various combinators 
    -- are implemented
    , Compose.RuleSelector(..)
    , Compose.selRules
    , Compose.selDPs
    , Compose.selStricts
    , Compose.selFirstCongruence
    , Compose.selFirstStrictCongruence
    , Compose.selFromCWDG
    , Compose.selFromWDG
    , Compose.selCombine
    , Compose.selUnion
    , Compose.selInter
    , Compose.selInverse
    , ComposeRC.defaultSelect
    -- *** Default Options
    , IsDefaultOption (..)
    , MatrixOptions (..)
    , PolyOptions (..)
    -- **** Specific Polynomials 
    , simplePolynomial 
    , linearPolynomial
    , stronglyLinearPolynomial
    , simpleMixedPolynomial
    , quadraticPolynomial
    , customPolynomial
      -- | Option for polynomials of custom shape, as defined by the first argument.
      -- This function receives a list of variables 
      -- denoting the @n@ arguments of the interpretation function. The return value of type ['Poly.SimpleMonomial']
      -- corresponds to the list of monomials of the constructed interpretation function.
      -- A polynomial is a list of unique 'Poly.SimpleMonomial', where 'Poly.SimpleMonomial' are 
      -- considered equal if the set variables together with powers match.
      -- 'SimpleMonomial' can be build using 'Poly.^^^', 'Poly.constant' and 'Poly.mono'.
      -- For instance, linear interpretations are constructed using the function 
      -- @ 
      -- \vs -> [constant] ++ [ v^^^1 | v <- vs]
      -- @
      -- . 
    , Poly.SimpleMonomial
     -- | A 'Poly.SimpleMonomial' denotes a monomial with variables in 'Variable', 
     -- and can be build using 'Poly.^^^', 'Poly.constant' and 'Poly.mono'.
    , (Poly.^^^)
      -- | @v ^^^ k@ denotes exponentiation of variable @v@ with constant @k@.
    , Poly.mono
      -- | @
      -- mono [v1^^^k1,...,vn^^^kn]
      -- @ 
      -- constructs the 'Poly.SimpleMonomial'
      -- @
      -- c * v1^k1 * ... * v1^kn
      -- @
      -- where @c@ is unique for the constructed monomial
    , Poly.boolCoefficient
      -- | returns a new monomial whose coefficient is guaranteed to be @0@ or @1@.
    , Poly.constant
      -- | returns a new monomial without variables.
      
      -- * Misc
    , solveBy -- MA:TODO

      -- * Existential Quantification
    , some 
    -- | Wrap an object by existential quantification.
    , EQuantified (..)
    -- | This class establishes a mapping between types and their existential 
    -- quantified counterparts
    )
where
import Control.Monad (liftM)
import Termlib.Problem (Problem)
import Termlib.Variable (Variable)
import qualified Tct.Method.Combinator as Combinators
import qualified Tct.Method.PopStar as PopStar
import qualified Tct.Method.EpoStar as EpoStar
import qualified Tct.Method.Compose as Compose
import qualified Tct.Method.ComposeRC as ComposeRC
import qualified Tct.Method.Bounds as Bounds
import qualified Tct.Method.Matrix.ArcticMI as ArcticMI
import qualified Qlogic.ArcSat as ArcSat
import qualified Tct.Method.DP.Simplification as DPSimp
import qualified Tct.Method.Matrix.NaturalMI as NaturalMI
import qualified Tct.Method.Poly.PolynomialInterpretation as Poly
import qualified Tct.Method.Poly.NaturalPI as NaturalPI
import qualified Tct.Method.Custom as Custom
import qualified Tct.Method.Predicates as Predicates
import qualified Tct.Method.Uncurry as Uncurry
import qualified Tct.Method.DP.UsableRules as UR
import qualified Tct.Method.DP.DependencyPairs as DP
import qualified Tct.Method.DP.PathAnalysis as PathAnalysis
import qualified Tct.Method.Weightgap as Weightgap
import qualified Tct.Method.DP.DependencyGraph as DG
import qualified Tct.Method.InnermostRuleRemoval as IRR
import Qlogic.NatSat (Size (..))
import qualified Tct.Processor as P
import qualified Tct.Processor.Standard as S
import Tct.Processor (solveBy)
import Tct.Processor.Args ((:+:)(..), Unit(..))
import Tct.Processor.Args.Instances (nat)
import Tct.Processor.Transformations hiding (withArgs)
import qualified Tct.Processor.Transformations as T
import qualified Tct.Processor.Timeout as Timeout

import Tct.Method.Combinator (ite, empty, fastest,sequentially)
import Tct.Method.Predicates (WhichTrs (..), isDuplicating)
-- combinators

step :: (Transformer t1, P.Processor a) =>
       [t] -> (t -> TheTransformer t1) -> (t -> P.InstanceOf a) -> P.InstanceOf P.SomeProcessor
step []     _ _ = some Combinators.empty
step (i:is) t p = some $ p i `before` (t i >>| step is t p)

upto :: (Enum n, Ord n, P.ComplexityProof (P.ProofOf p), P.Processor p) =>
        (n -> P.InstanceOf p) -> (Bool :+: n :+: n) -> P.InstanceOf (S.StdProcessor (Combinators.OneOf p))
upto prc (fast :+: l :+: u) | l > u     = Combinators.fastest []
                            | fast      = Combinators.fastest subs
                            | otherwise = Combinators.sequentially subs
    where subs = [ prc i | i <- [l..u] ]

orFaster :: (P.Processor a, P.Processor b) => 
           P.InstanceOf a -> P.InstanceOf b -> P.InstanceOf (S.StdProcessor (Combinators.OneOf P.SomeProcessor))
a `orFaster` b = Combinators.fastest [P.someInstance a, P.someInstance b]

orBetter :: (P.Processor a, P.Processor b) => 
           P.InstanceOf a -> P.InstanceOf b -> P.InstanceOf (S.StdProcessor (Combinators.OneOf P.SomeProcessor))
a `orBetter` b = Combinators.best [P.someInstance a, P.someInstance b]

before :: (P.Processor a, P.Processor b) => 
           P.InstanceOf a -> P.InstanceOf b -> P.InstanceOf (S.StdProcessor (Combinators.OneOf P.SomeProcessor))
a `before` b = Combinators.sequentially [P.someInstance a, P.someInstance b]


dpsimps :: TheTransformer SomeTransformation
dpsimps   = try DPSimp.removeTails >>> try DPSimp.simpDPRHS >>> UR.usableRules

class IsDefaultOption a where
    defaultOptions :: a

-- * defaultMatrix

data MatrixOptions = MatrixOptions { cert :: NaturalMI.NaturalMIKind -- ^ defines how the induced certificate is computed.
                                   , dim  :: Int -- ^ dimension of matrix coefficients. The default is 'Algebraic'.
                                   , degree :: Maybe Int -- ^ upper bound on degree of induced certificate, cf. also cert. The default is @2@.
                                   , bits :: Int -- ^ number of bits used for encoding entries in coefficient matrix. The default is @2@.
                                   , cbits :: Maybe Int -- ^ number of bits used for intermediate results. The default is @Just 3@. If @Nothing@ is given then sizes of intermediate results are not restricted.
                                   , on :: Weightgap.WgOn -- ^ option solely for weightgap
                                   , useUsableArgs :: Bool -- ^ Defines whether monotonicity-constraints are weakened by taking usable argument positions into account. The default is @True@ 
                                   }

instance IsDefaultOption MatrixOptions where 
    defaultOptions = MatrixOptions { cert   = NaturalMI.Algebraic
                                   , dim    = 2
                                   , degree = Nothing
                                   , bits   = 2
                                   , cbits  = Just $ 3
                                   , useUsableArgs = True
                                   , on            = Weightgap.WgOnAny }

matrix :: MatrixOptions -> P.InstanceOf (S.StdProcessor NaturalMI.NaturalMI)
matrix m = S.StdProcessor NaturalMI.NaturalMI `S.withArgs` (cert m :+: (nat `liftM` degree m) :+: nat (dim m) :+: nat (bits m) :+: Nothing :+: (nat `liftM` cbits m) :+: useUsableArgs m)


arctic :: MatrixOptions -> P.InstanceOf (S.StdProcessor ArcticMI.ArcticMI)
arctic m = S.StdProcessor ArcticMI.ArcticMI `S.withArgs` (nat (dim m) :+: (nat $ ArcSat.intbound $ ArcSat.Bits $ bits m) :+: Nothing :+: (nat `liftM` cbits m) :+: useUsableArgs m)


weightgap :: MatrixOptions -> T.TheTransformer Weightgap.WeightGap
weightgap m = T.Transformation Weightgap.WeightGap `T.withArgs` (on m :+: (cert m) :+: (nat `liftM` degree m) :+: (nat $ dim m) :+: (nat $ bits m) :+: Nothing :+: (nat `liftM` cbits m) :+: (useUsableArgs m))

-- * defaultPoly

data PolyOptions = PolyOptions { pkind :: Poly.PolyShape
                               , pbits :: Int
                               , pcbits :: Maybe Int
                               , puseUsableArgs :: Bool }

instance IsDefaultOption PolyOptions where
  defaultOptions = PolyOptions { pkind          = Poly.SimpleShape Poly.Simple
                               , pbits          = 2
                               , pcbits         = Just 3
                               , puseUsableArgs = True }

simplePolynomial :: PolyOptions
simplePolynomial = defaultOptions { pkind = Poly.SimpleShape Poly.Simple }

linearPolynomial :: PolyOptions
linearPolynomial = defaultOptions { pkind = Poly.SimpleShape Poly.Linear }

stronglyLinearPolynomial :: PolyOptions
stronglyLinearPolynomial = defaultOptions { pkind = Poly.SimpleShape Poly.StronglyLinear }

simpleMixedPolynomial :: PolyOptions
simpleMixedPolynomial = defaultOptions { pkind = Poly.SimpleShape Poly.SimpleMixed }

quadraticPolynomial :: PolyOptions
quadraticPolynomial = defaultOptions { pkind = Poly.SimpleShape Poly.Quadratic } 

customPolynomial :: ([Variable] -> [Poly.SimpleMonomial]) -> PolyOptions
customPolynomial mk = defaultOptions { pkind = Poly.CustomShape mk}

poly :: PolyOptions -> P.InstanceOf (S.StdProcessor NaturalPI.NaturalPI)
poly p = S.StdProcessor NaturalPI.NaturalPI `S.withArgs` (pkind p :+: nat 3 :+: Just (nat (pbits p)) :+: nat `liftM` pcbits p :+: puseUsableArgs p)


withProblem :: P.Processor proc =>
              (Problem -> P.InstanceOf proc) -> P.InstanceOf (Custom.CustomProcessor Unit (P.ProofOf proc))
withProblem f = Custom.customInstance "Inspecting Problem..." (\ prob -> P.solve (f prob) prob)


-- * existential quantification 

class EQuantified a where 
    type EQuantifiedOf a
    equantify :: a -> (EQuantifiedOf a)

instance Transformer t => EQuantified (T.TheTransformer t) where
    type EQuantifiedOf (T.TheTransformer t) = T.TheTransformer SomeTransformation
    equantify t = T.someTransformation t

instance P.Processor p => EQuantified (P.InstanceOf p) where
    type EQuantifiedOf (P.InstanceOf p) = P.InstanceOf P.SomeProcessor
    equantify p = P.someInstance p


some :: EQuantified a => a -> EQuantifiedOf a
some = equantify


-- * Competition Strategy 


dos :: MatrixOptions
dos   = defaultOptions { cbits = Just 4, bits = 3}

lin :: MatrixOptions
lin   = dos { dim = 1, degree = Just 1}

quad :: MatrixOptions
quad  = dos { dim = 2, degree = Nothing}

cubic :: MatrixOptions
cubic = dos { dim = 3, degree = Nothing}

quartic :: MatrixOptions
quartic = dos { dim = 4, degree = Nothing}

quintic :: MatrixOptions
quintic = dos { dim = 5, degree = Nothing}

te :: Transformer t => TheTransformer t -> TheTransformer (Try SomeTransformation)
te = try . exhaustively

dc2011 :: P.InstanceOf P.SomeProcessor
dc2011 = some $ Custom.named "dc2011" $ ite (isDuplicating Strict) Combinators.fail strategy
      where matrices simple c | simple = empty `before` fastest [matrix defaultOptions {dim = i, degree = Nothing, cbits= Just 4, bits=3, cert=c} | i <- [1..bound]]
                              | otherwise = empty `before` fastest [ matrix defaultOptions {dim = i, degree = Just j, cbits= Just 4, bits=3, cert=c} | (i,j) <- zip [1..bound] [1..]]
            bound       = 6
            direct      = matrices False NaturalMI.Algebraic
            insidewg    = matrices False NaturalMI.Algebraic
            matchbounds = Bounds.bounds Bounds.Minimal Bounds.Match 
                          `orFaster` Bounds.bounds Bounds.PerSymbol Bounds.Match
            wgs         = weightgap lin 
                          <> weightgap quad
                          <> weightgap cubic
                          <> weightgap quartic
                          <> weightgap quintic
            strategy    = try IRR.irr 
                          >>| try Uncurry.uncurry 
                          >>| (direct 
                               `orFaster` (te wgs >>| insidewg) 
                               `orFaster` matchbounds)

rc2011 :: P.InstanceOf P.SomeProcessor
rc2011 = some $ Custom.named "rc2011" $ ite Predicates.isInnermost (rc DP.dependencyTuples) (rc DP.dependencyPairs)
    where rc mkdp = try IRR.irr >>| matricesBlockOf 2 `orFaster` matchbounds `orFaster` dp mkdp
          matricesForDegree deg = [ matrix defaultOptions {dim = n, degree = Just deg} | n <- [deg..if deg > 3 then deg else (deg + 3)]] -- matrices for degree deg
          
          matricesBlockOf l = fastest [ sequentially $ concatMap (\ j -> matricesForDegree (i + (j * l))) [0..] | i <- [1..max 1 l]] 
          -- fastest [ sequentially (matricesForDegree 1 ++ matricesForDegree (1 + l) ++ matricesForDegree (1 + 2l) ...  ] 
          --           , ..., 
          --           sequentially (matricesForDegree l ++ matricesForDegree (l + l) ++ matricesForDegree (l + 2l) ...  ] 
          -- dh l prozesse laufen parallel, und im rad sequentiell
          
          
          matchbounds = Timeout.timeout 5 (Bounds.bounds Bounds.Minimal Bounds.Match 
                                           `orFaster` Bounds.bounds Bounds.PerSymbol Bounds.Match)
          
          dp mkdp = mkdp
                     >>| UR.usableRules 
                     >>| (insideDP 
                         `orFaster` (PathAnalysis.pathAnalysis >>|| UR.usableRules >>| insideDP))
             where insideDP  = te dpsimps >>| empty `before` (try wgUsables >>| te (try dpsimps >>> wgAll) >>| directs)
                   wgAll     = weightgap lin 
                               <> weightgap quad
                               <> weightgap cubic
                   wgUsables = weightgap lin {on = Weightgap.WgOnTrs} 
                               <> weightgap quad {on = Weightgap.WgOnTrs} 
                               <> weightgap cubic {on = Weightgap.WgOnTrs}
                   -- composeMult = compose splitWithoutLeafs Mult elim 
                   -- elim     = P.someInstance (try dpsimp >>| directs `before` insideDP) -- arrr
                   
                   directs  = empty `before` (matricesBlockOf 3 `orFaster` matchbounds)

