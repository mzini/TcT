{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeFamilies #-}

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
      -- Configuration parameters for both types of options are collected in 'MatrixOptions', supply 'defaultOptions'
      -- for using matrix interpretations with default parameters.
    , arctic
    , matrix
      
    , MatrixOptions (..)
    , NaturalMI.NaturalMIKind (..)
    , Weightgap.WgOn (..)

      -- *** Polynomial Interpretations
      -- | TcT implements /polynomial interpretations over natural numbers/.
      -- Configuration parameters are collected in 'PolyOptions', supply 'defaultOptions'
      -- for using plynomial interpretations with default parameters.
    , poly
    , PolyOptions (..)
      -- | The shape of a polynomial influences the computed certificate, 
      -- but has also severe impacts on the time spend on proof search.
      -- In the following, we collect some common shapes of polynomials found
      -- in the literature. Custom shapes can be used with options 'customPolynomial'.
    , simplePolynomial 
    , linearPolynomial
    , stronglyLinearPolynomial
    , simpleMixedPolynomial
    , quadraticPolynomial
    , customPolynomial
    , Poly.SimpleMonomial
    , (Poly.^^^)
    , Poly.mono
    , Poly.boolCoefficient
    , Poly.constant
      
      -- ** Processors Based on Recursive Path Orderings
    , EpoStar.epostar
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
    , withProblem
    , named
      
      -- ** Combinators Guiding the Proof Search
    , Timeout.timeout
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
      
      -- * Competition Strategies 
    , rc2011
      -- | This processor reflects the runtime complexity strategy employed in the competition 2011.
    , dc2011
      -- | This processor reflects the derivational complexity strategy employed in the competition 2011.
      
      -- * Transformations #MethodsTrans#
      -- | This section list all instances of 'Transformation'. A transformation 't' 
      -- is lifted to a 'P.Processor' using the combinator '>>|' or '>>||'.
      
      -- ** Lifting of Transformations to Processors
    , (T.>>|)    
    , (T.>>||)      
      
      -- ** Combinators     
      -- | Following Combinators work on transformations.
    , T.try
    , (T.>>>)
    , (T.<>)      
    , exhaustively
    , T.idtrans
      
      -- ** Innermost Rule Removal
    , IRR.irr
      
      -- ** 
    , TOI.toInnermost
      
      -- ** Uncurrying
    , Uncurry.uncurry
      
      -- ** Weightgap
    , weightgap
      
      -- ** Compose
    , Compose.compose
    , Compose.composeDynamic
    , Compose.composeStatic
    , ComposeRC.composeRC
    , Compose.ComposeBound (..)
    , Compose.Partitioning (..)
    , ComposeRC.composeRCselect
    , ComposeRC.solveAWith
    , ComposeRC.solveBWith
    -- *** RuleSelector
    -- | A 'Compose.RuleSelector' is used to select 
    -- rules from a problem. Various combinators 
    -- are implemented.
    , RS.RuleSelector      
    , RS.selRules
    , RS.selDPs
    , RS.selStricts
    , RS.selWeaks
    , RS.selFromWDG
    , RS.selFromCWDG
    , RS.selFirstCongruence
    , RS.selFirstStrictCongruence
    , RS.selCombine 
    , RS.selInverse
    , RS.selUnion
    , RS.selInter
      
      -- ** Weak Dependency Pairs
    , DP.dependencyPairs
    , DP.dependencyTuples
      -- ** DP Transformations      
      -- | The following transformations only work on dependency pair problems, 
      -- as obtained by 'DP.dependencyPairs' and 'DP.dependencyTuples'.
    , pathAnalysis      
    , linearPathAnalysis
    , UR.usableRules
    , DPSimp.removeTails
    , DPSimp.simpDPRHS      
    , DPSimp.simpKP
    , dpsimps
    , DG.Approximation(..)

    -- * Default Options
    , IsDefaultOption (..)
      
      -- * Existential Quantification
    , some 
    , solveBy
    , EQuantified (..)
    )
where
import Control.Monad (liftM)
import Termlib.Problem (Problem)
import Termlib.Variable (Variable)
import qualified Tct.Method.Combinator as Combinators
import qualified Tct.Method.PopStar as PopStar
import qualified Tct.Method.Mpo as Mpo
import qualified Tct.Method.EpoStar as EpoStar
import qualified Tct.Method.Compose as Compose
import qualified Tct.Method.ComposeRC as ComposeRC
import qualified Tct.Method.Bounds as Bounds
import qualified Tct.Method.Bounds.Automata as Bounds.Automata
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
import qualified Tct.Method.ToInnermost as TOI
import qualified Tct.Method.RuleSelector as RS
import qualified Tct.Processor as P
import qualified Tct.Processor.Standard as S
import qualified Tct.Method.Timeout as Timeout
import Tct.Processor (solveBy)
import Tct.Processor.Args ((:+:)(..), Unit(..))
import Tct.Processor.Args.Instances (nat)
import Tct.Processor.Transformations hiding (withArgs)
import qualified Tct.Processor.Transformations as T


import Tct.Method.Combinator (ite, empty, fastest,sequentially)
import Tct.Method.Predicates (WhichTrs (..), isDuplicating)

-- TODO doc
pathAnalysis :: TheTransformer PathAnalysis.PathAnalysis
pathAnalysis = PathAnalysis.pathAnalysis False

-- TODO doc
linearPathAnalysis :: TheTransformer PathAnalysis.PathAnalysis
linearPathAnalysis = PathAnalysis.pathAnalysis True


-- | 'named name proc' acts like 'proc', but displays itself under the name 'name' in proof outputs      
named :: P.Processor proc => String -> P.InstanceOf proc -> P.InstanceOf P.SomeProcessor
named n inst = some $ proc `S.withArgs` ()
  where proc = Custom.fromAction d (\ () -> P.solve inst)
        d    = Custom.Description { Custom.as    = n
                                  , Custom.descr = []
                                  , Custom.args  = Unit }

-- | The instance @withProblem mkproc@ allows the creation of a processor 
-- depending on the problem it should handle.
withProblem :: P.Processor proc => (Problem -> P.InstanceOf proc) -> P.InstanceOf (S.StdProcessor (Custom.Custom Unit (P.ProofOf proc)))
withProblem f = proc `S.withArgs` ()
  where proc = Custom.fromAction d (\ () prob -> P.solve (f prob) prob )
        d    = Custom.Description { Custom.as    = "Inspecting Problem..."
                                  , Custom.descr = []
                                  , Custom.args  = Unit }

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
step :: (Transformer t1, P.Processor a) =>
       [t] -> (t -> TheTransformer t1) -> (t -> P.InstanceOf a) -> P.InstanceOf P.SomeProcessor
step []     _ _ = some Combinators.empty
step (i:is) t p = some $ p i `Combinators.before` (t i >>| empty `Combinators.before` step is t p)


-- | @
-- upto mkproc (b :+: l :+: u) == f [ mkproc i | i <- [l..u]] 
-- @ 
-- where 
-- @f == fastest@ if @b == True@ and @f == sequentially@ otherwise.
upto :: (Enum n, Ord n, P.ComplexityProof (P.ProofOf p), P.Processor p) =>
        (n -> P.InstanceOf p) -> (Bool :+: n :+: n) -> P.InstanceOf (S.StdProcessor (Combinators.OneOf p))
upto prc (fast :+: l :+: u) | l > u     = Combinators.fastest []
                            | fast      = Combinators.fastest subs
                            | otherwise = Combinators.sequentially subs
    where subs = [ prc i | i <- [l..u] ]


-- | Fast simplifications based on dependency graph analysis.
dpsimps :: TheTransformer SomeTransformation
dpsimps   = try DPSimp.removeTails 
            >>> try DPSimp.simpDPRHS 
            >>> try DPSimp.simpKP            
            >>> try UR.usableRules

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

-- | This processor implements matrix interpretations.     
matrix :: MatrixOptions -> P.InstanceOf (S.StdProcessor NaturalMI.NaturalMI)
matrix m = S.StdProcessor NaturalMI.NaturalMI `S.withArgs` (cert m :+: (nat `liftM` degree m) :+: nat (dim m) :+: nat (bits m) :+: Nothing :+: (nat `liftM` cbits m) :+: useUsableArgs m)

-- | This processor implements arctic interpretations.
arctic :: MatrixOptions -> P.InstanceOf (S.StdProcessor ArcticMI.ArcticMI)
arctic m = S.StdProcessor ArcticMI.ArcticMI `S.withArgs` (nat (dim m) :+: (nat $ ArcSat.intbound $ ArcSat.Bits $ bits m) :+: Nothing :+: (nat `liftM` cbits m) :+: useUsableArgs m)


-- | This processor implements the weightgap principle.   
weightgap :: MatrixOptions -> T.TheTransformer Weightgap.WeightGap
weightgap m = T.Transformation Weightgap.WeightGap `T.withArgs` (on m :+: (cert m) :+: (nat `liftM` degree m) :+: (nat $ dim m) :+: (nat $ bits m) :+: Nothing :+: (nat `liftM` cbits m) :+: (useUsableArgs m))

-- * defaultPoly

data PolyOptions = PolyOptions { pkind :: Poly.PolyShape -- ^ The shape of the constructed polynomial interpretation. The default is the simple shape 'Poly.Simple'.
                               , pbits :: Int -- ^ Number of bits for coefficients in SAT encoding. The default is '2'.
                               , pcbits :: Maybe Int -- ^ Number of bits for intermediate results in SAT encoding. 
                                                    -- Set to 'Nothing' for no bound on number of bits. The default is 'Just 3'.
                               , puseUsableArgs :: Bool -- ^ Defines whether monotonicity-constraints are weakened by taking usable argument positions into account. The default is True 
                               }

instance IsDefaultOption PolyOptions where
  defaultOptions = PolyOptions { pkind          = Poly.SimpleShape Poly.Simple
                               , pbits          = 2
                               , pcbits         = Just 3
                               , puseUsableArgs = True }

-- | Options for @simple@ polynomial interpretations.
simplePolynomial :: PolyOptions
simplePolynomial = defaultOptions { pkind = Poly.SimpleShape Poly.Simple }

-- | Options for @linear@ polynomial interpretations.
linearPolynomial :: PolyOptions
linearPolynomial = defaultOptions { pkind = Poly.SimpleShape Poly.Linear }

-- | Options for @strongly linear@ polynomial interpretations.
stronglyLinearPolynomial :: PolyOptions
stronglyLinearPolynomial = defaultOptions { pkind = Poly.SimpleShape Poly.StronglyLinear }

-- | Options for @simple mixed@ polynomial interpretations.
simpleMixedPolynomial :: PolyOptions
simpleMixedPolynomial = defaultOptions { pkind = Poly.SimpleShape Poly.SimpleMixed }

-- | Options for @quadratic mixed@ polynomial interpretations.
quadraticPolynomial :: PolyOptions
quadraticPolynomial = defaultOptions { pkind = Poly.SimpleShape Poly.Quadratic } 

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
customPolynomial :: ([Variable] -> [Poly.SimpleMonomial]) -> PolyOptions
customPolynomial mk = defaultOptions { pkind = Poly.CustomShape mk}

-- | This processor implements polynomial interpretations.
poly :: PolyOptions -> P.InstanceOf (S.StdProcessor NaturalPI.NaturalPI)
poly p = NaturalPI.polyProcessor `S.withArgs` (pkind p :+: nat 3 :+: Just (nat (pbits p)) :+: nat `liftM` pcbits p :+: puseUsableArgs p)




-- * existential quantification 

-- | This class establishes a mapping between types and their existential 
-- quantified counterparts.
class EQuantified a where 
    type EQuantifiedOf a
    equantify :: a -> (EQuantifiedOf a)

instance Transformer t => EQuantified (T.TheTransformer t) where
    type EQuantifiedOf (T.TheTransformer t) = T.TheTransformer SomeTransformation
    equantify t = T.someTransformation t

instance P.Processor p => EQuantified (P.InstanceOf p) where
    type EQuantifiedOf (P.InstanceOf p) = P.InstanceOf P.SomeProcessor
    equantify p = P.someInstance p

-- | Wrap an object by existential quantification.
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
dc2011 = some $ named "dc2011" $ ite (isDuplicating Strict) Combinators.fail strategy
      where matrices simple c | simple = empty `Combinators.before` fastest [matrix defaultOptions {dim = i, degree = Nothing, cbits= Just 4, bits=3, cert=c} | i <- [1..bound]]
                              | otherwise = empty `Combinators.before` fastest [ matrix defaultOptions {dim = i, degree = Just j, cbits= Just 4, bits=3, cert=c} | (i,j) <- zip [1..bound] [1..]]
            bound       = 6
            direct      = matrices False NaturalMI.Algebraic
            insidewg    = matrices False NaturalMI.Algebraic
            matchbounds = Bounds.bounds Bounds.Minimal Bounds.Match 
                          `Combinators.orFaster` Bounds.bounds Bounds.PerSymbol Bounds.Match
            wgs         = weightgap lin 
                          <> weightgap quad
                          <> weightgap cubic
                          <> weightgap quartic
                          <> weightgap quintic
            strategy    = try IRR.irr 
                          >>| try Uncurry.uncurry 
                          >>| (direct 
                               `Combinators.orFaster` (te wgs >>| insidewg) 
                               `Combinators.orFaster` matchbounds)

rc2011 :: P.InstanceOf P.SomeProcessor
rc2011 = some $ named "rc2011" $ ite Predicates.isInnermost (rc DP.dependencyTuples) (rc DP.dependencyPairs)
    where rc mkdp = try IRR.irr >>| matricesBlockOf 2 `Combinators.orFaster` matchbounds `Combinators.orFaster` dp mkdp
          matricesForDegree deg = [ matrix defaultOptions {dim = n, degree = Just deg} | n <- [deg..if deg > 3 then deg else (deg + 3)]] -- matrices for degree deg
          
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
                               >>> try DPSimp.simpKP                   
                   wgAll     = weightgap lin 
                               <> weightgap quad
                               <> weightgap cubic
                   wgUsables = weightgap lin {on = Weightgap.WgOnTrs} 
                               <> weightgap quad {on = Weightgap.WgOnTrs} 
                               <> weightgap cubic {on = Weightgap.WgOnTrs}
                   -- composeMult = compose splitWithoutLeafs Mult elim 
                   -- elim     = P.someInstance (try dpsimp >>| directs `Combinators.before` insideDP) -- arrr
                   
                   directs  = empty `Combinators.before` (matricesBlockOf 3 `Combinators.orFaster` matchbounds)

