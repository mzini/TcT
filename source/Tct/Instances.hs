{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeOperators #-}

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
    , polys
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
      
      -- * Transformations #MethodsTrans#
      -- | This section list all instances of 'Transformation'. A transformation 't' 
      -- is lifted to a 'P.Processor' using the combinator '>>|' or '>>||'.
      
      -- ** Lifting of Transformations to Processors
    , (T.>>|)    
    , (>>!)          
    , (T.>>||)
    , (>>!!)                
      
      -- ** Combinators     
      -- | Following Combinators work on transformations.
    , TCombinator.try
    , (TCombinator.>>>)
    , (TCombinator.<>)      
    , (TCombinator.<||>)            
    , TCombinator.exhaustively
    , te
    , when
    , TCombinator.idtrans
      
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
    , partitionIndependent
    , Compose.composeDynamic
    , Compose.composeStatic      
    , Compose.greedy      
    , ComposeRC.composeRC
    , Compose.ComposeBound (..)
    , ComposeRC.composeRCselect
    , ComposeRC.solveAWith
    , ComposeRC.solveBWith
    -- *** RuleSelector
    -- | A 'Compose.RuleSelector' is used to select 
    -- rules from a problem. Various combinators 
    -- are implemented.
    , RS.RuleSelector (..)
    , RS.RuleSetSelector
    , RS.ExpressionSelector
      
      -- * Primitives
    , RS.selRules
    , RS.selDPs
    , RS.selStricts
    , RS.selWeaks
      -- * Constructors
    , RS.selFromWDG
    , RS.selFromCWDG
      -- * Combinators
    , RS.selInverse
    , RS.selCombine
    , RS.selUnion
    , RS.selInter
      -- * Rule-selectors based on dependency graphs
    , RS.selFirstCongruence
    , RS.selFirstStrictCongruence
    , selFWBWstrict
      -- * Boolean Selectors
    , RS.selAnyOf
    , RS.selAllOf
    , RS.selAnd
    , RS.selOr
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
    , DPSimp.removeHeads      
    , DPSimp.trivial      
    , DPSimp.removeInapplicable      
    , DPSimp.simpDPRHS      
    , DPSimp.simpKP
    , DPSimp.simpKPOn
    , DPSimp.withKPOn
    -- , DPSimp.inline      
    , dpsimps
    , toDP
    , removeLeaf
    , DG.Approximation(..)

      
    -- * Default Options
    , IsDefaultOption (..)
      
      -- * Operations on Processors and Transformations
    , TimesOut (..)
    , WithProblem (..)
    , withWDG
    , withCWDG
    , EQuantified (..)
    , some 
    , solveBy
    )
where
  
import Control.Monad (liftM)
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
import Tct.Processor.Transformations ((>>|), (>>||))
import qualified Tct.Processor.Transformations as T
import qualified Tct.Method.TCombinator as TCombinator
import Tct.Method.TCombinator ((>>>),(<>),(<||>),try, exhaustively)

import Tct.Method.Combinator (ite, empty, fastest,sequentially)
import Tct.Method.Predicates (WhichTrs (..), isDuplicating)
import qualified Tct.Certificate as Cert

import Termlib.Problem (Problem)
import qualified Termlib.Problem as Prob
import qualified Termlib.Trs as Trs

import qualified Data.List as List
import qualified Data.Set as Set

-- TODO doc
pathAnalysis :: T.TheTransformer PathAnalysis.PathAnalysis
pathAnalysis = PathAnalysis.pathAnalysis False

-- TODO doc
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
        (n -> P.InstanceOf p) -> (Bool :+: n :+: n) -> P.InstanceOf (S.StdProcessor (Combinators.OneOf p))
upto prc (fast :+: l :+: u) | l > u     = Combinators.fastest []
                            | fast      = Combinators.fastest subs
                            | otherwise = Combinators.sequentially subs
    where subs = [ prc i | i <- [l..u] ]



bsearch :: P.Processor proc => String -> (Maybe Int -> P.InstanceOf proc) -> P.InstanceOf (S.StdProcessor (Custom.Custom Unit (P.ProofOf proc)))
bsearch nm mkinst = bsearchProcessor `S.withArgs` ()
  where bsearchProcessor = Custom.fromAction 
                           Custom.Description { Custom.as = "bsearch-"++nm
                                              , Custom.descr = []
                                              , Custom.args = Unit }
                           (const $ bsearch' mkinst)
        bsearch' mk prob = 
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


partitionIndependent :: T.TheTransformer (Compose.Compose P.AnyProcessor)
partitionIndependent = Compose.composeStatic selFWBWstrict Compose.Add

selFWBWstrict :: RS.ExpressionSelector
selFWBWstrict = RS.selAllOf $ RS.selFromWDG "forward and backward closed partitioning of WDG" f
  where f wdg = case stricts of 
                  [] -> Prob.emptyRuleset 
                  n:_ -> Prob.emptyRuleset 
                          {Prob.sdp = Trs.fromRules [ r | (_,(DG.StrictDP, r)) <- DG.withNodeLabels' wdg $ rs n] }
          where stricts = [n | (n,(DG.StrictDP,_)) <- DG.lnodes wdg]
                iwdg = DG.inverse wdg
                rs n = DG.reachablesBfs wdg [n] `union` DG.reachablesBfs iwdg [n]
        a `union` b = Set.toList $ Set.fromList a `Set.union` Set.fromList b

-- | Fast simplifications based on dependency graph analysis.
dpsimps :: T.TheTransformer T.SomeTransformation
dpsimps   = try DPSimp.removeTails 
            -- >>> try DPSimp.inline
            >>> te DPSimp.removeHeads
            >>> te DPSimp.removeInapplicable
            >>> try DPSimp.simpDPRHS 
            >>> try UR.usableRules
            >>> try DPSimp.trivial
            
-- | use 'DPSimp.simpKPOn' and 'DPSimp.removeTails' to remove leafs from the dependency graph. 
cleanTail :: T.TheTransformer T.SomeTransformation
cleanTail = 
  te (DPSimp.simpKPOn RS.selStrictLeafs) 
  >>> try (DPSimp.removeTails >>> try DPSimp.simpDPRHS)
            
-- | Tries dependency pairs with weightgap, otherwise uses dependency tuples. 
-- Simpifies the resulting DP problem as much as possible.
toDP :: T.TheTransformer T.SomeTransformation
toDP = 
  try (timeout 5 dps <> dts)
  >>> try DPSimp.removeInapplicable
  >>> try cleanTail
  >>> te DPSimp.removeHeads
  >>> te partitionIndependent
  >>> try cleanTail
  >>> try DPSimp.trivial
  >>> try UR.usableRules
  where 
    dps = DP.dependencyPairs >>> try UR.usableRules >>> wgOnUsable
    dts = DP.dependencyTuples
    wgOnUsable = Compose.composeDynamic Compose.Add $ 
                 weightgap defaultOptions { dim = 2
                                          , degree = (Just 1)
                                          , on = Weightgap.WgOnTrs }



-- | removes leafs in the dependency graph, using knowledge-propagation
-- and the given processor        
removeLeaf :: P.Processor p => P.InstanceOf p -> T.TheTransformer T.SomeTransformation
removeLeaf p = 
  p `DPSimp.withKPOn` RS.selAnyLeaf
  >>> try (DPSimp.removeTails >>> try DPSimp.simpDPRHS)
  >>> try UR.usableRules
  >>> try DPSimp.trivial

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
                                   , useUsableRules :: Bool -- ^ Defines wether usable rules modula argument filtering should be used. (only NaturalMI)
                                   }

instance IsDefaultOption MatrixOptions where 
    defaultOptions = MatrixOptions { cert   = NaturalMI.Algebraic
                                   , dim    = 2
                                   , degree = Nothing
                                   , bits   = 2
                                   , cbits  = Just $ 3
                                   , useUsableArgs = True
                                   , useUsableRules = True
                                   , on            = Weightgap.WgOnAny }

-- | This processor implements matrix interpretations.     
matrix :: MatrixOptions -> P.InstanceOf (S.StdProcessor NaturalMI.NaturalMI)
matrix m = S.StdProcessor NaturalMI.NaturalMI `S.withArgs` (cert m :+: (nat `liftM` degree m) :+: nat (dim m) :+: nat (bits m) :+: Nothing :+: (nat `liftM` cbits m) :+: useUsableArgs m :+: useUsableRules m)

-- | This processor implements arctic interpretations.
arctic :: MatrixOptions -> P.InstanceOf (S.StdProcessor ArcticMI.ArcticMI)
arctic m = S.StdProcessor ArcticMI.ArcticMI `S.withArgs` (nat (dim m) :+: (nat $ ArcSat.intbound $ ArcSat.Bits $ bits m) :+: Nothing :+: (nat `liftM` cbits m) :+: useUsableArgs m)


-- TODO: check if urules are applicable
-- | This processor implements the weightgap principle.   
weightgap :: MatrixOptions -> P.InstanceOf (S.StdProcessor Weightgap.WeightGap)
weightgap m = S.StdProcessor Weightgap.WeightGap `S.withArgs` (on m :+: (cert m) :+: (nat `liftM` degree m) :+: (nat $ dim m) :+: (nat $ bits m) :+: Nothing :+: (nat `liftM` cbits m) :+: useUsableArgs m :+: useUsableRules m)

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

-- | 'polys n' defines a suitable polynomial of degree 'n'
polys :: Int -> P.InstanceOf (S.StdProcessor NaturalPI.NaturalPI)  
polys 1 = poly linearPolynomial
polys n = poly $ (customPolynomial inter) { pbits = 2, pcbits = Nothing }
  where inter vs = [ Poly.mono [(Poly.^^^) v 1 | v <- vs']
                   | vs' <- List.subsequences vs
                   , length vs <= n ]
                   ++ [Poly.mono [(Poly.^^^) v 2] | v <- vs] 

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


-- * Competition Strategies

-- | Shorthand for 'try . exhaustively'
te :: T.Transformer t => T.TheTransformer t -> T.TheTransformer (TCombinator.Try T.SomeTransformation)
te = try . exhaustively

dc2011 :: P.InstanceOf P.SomeProcessor
dc2011 = some $ named "dc2011" $ ite (isDuplicating Strict) Combinators.fail strategy
      where matrices simple c 
              | simple = empty `Combinators.before` fastest [matrix defaultOptions {dim = i, degree = Nothing, cbits= Just 4, bits=3, cert=c} 
                                                            | i <- [1..bound]]
              | otherwise = empty `Combinators.before` fastest [ matrix defaultOptions {dim = i, degree = Just j, cbits= Just 4, bits=3, cert=c} 
                                                               | (i,j) <- zip [1..bound] [1..]]
            bound       = 6
            direct      = matrices False NaturalMI.Algebraic
            insidewg    = matrices False NaturalMI.Algebraic
            matchbounds = Bounds.bounds Bounds.Minimal Bounds.Match 
                          `Combinators.orFaster` Bounds.bounds Bounds.PerSymbol Bounds.Match
                          
            dos   = defaultOptions { cbits = Just 4, bits = 3}
            lin   = dos { dim = 1, degree = Just 1}
            quad  = dos { dim = 2, degree = Nothing}
            cubic = dos { dim = 3, degree = Nothing}
            quartic = dos { dim = 4, degree = Nothing}
            quintic = dos { dim = 5, degree = Nothing}
                          
            wgs         = wg lin
                          <> wg quad
                          <> wg cubic
                          <> wg quartic
                          <> wg quintic
            wg = Compose.composeDynamic Compose.Add . weightgap
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
                        
          dos   = defaultOptions { cbits = Just 4, bits = 3}
          lin   = dos { dim = 1, degree = Just 1}
          quad  = dos { dim = 2, degree = Nothing}
          cubic = dos { dim = 3, degree = Nothing}
          
          dp mkdp = mkdp
                     >>| UR.usableRules 
                     >>| (insideDP 
                         `Combinators.orFaster` (PathAnalysis.pathAnalysis False >>|| UR.usableRules >>| insideDP))
             where insideDP  = te dpsimps' >>| empty `Combinators.before` (try wgUsables >>| te (try dpsimps' >>> wgAll) >>| directs)
                   dpsimps'  = try DPSimp.removeTails 
                               >>> try DPSimp.simpDPRHS 
                               >>> try DPSimp.simpKP                   
                   wgAll     = wg lin 
                               <> wg quad
                               <> wg cubic
                   wgUsables = wg lin {on = Weightgap.WgOnTrs} 
                               <> wg quad {on = Weightgap.WgOnTrs} 
                               <> wg cubic {on = Weightgap.WgOnTrs}
                   wg = Compose.composeDynamic Compose.Add . weightgap                               
                   -- composeMult = compose splitWithoutLeafs Mult elim 
                   -- elim     = P.someInstance (try dpsimp >>| directs `Combinators.before` insideDP) -- arrr
                   
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
                     , some $ timeout 59 $ fastest [matrix defaultOptions {dim = i, degree = Nothing, cbits= Just 4, bits=3, cert=NaturalMI.Algebraic} 
                                                   | i <- [1..3] ]
                     , some $ timeout 59 $ bsearch "matrix" (mmx 4)
                     , some $ timeout 59 $ Combinators.iteProgress mxs (dc2012' fastest) empty
                     , some $ timeout 59 $ del >>| dc2012' fastest
                     , some $ timeout 10 matchbounds
                     ]
                      
        matchbounds = Bounds.bounds Bounds.Minimal Bounds.Match 
                      `Combinators.orFaster` Bounds.bounds Bounds.PerSymbol Bounds.Match

        dos dimension degr = defaultOptions { cbits = Just (bits' + 1)
                                            , bits = bits'
                                            , cert = cert'
                                            , dim = dim'
                                            , degree = if dim' > deg' then Just deg' else Nothing }
          where bits' | dimension <= 3 = 3
                      | otherwise = 1
                dim' = max 1 dimension
                deg' = max 0 degr
                cert' | deg' == 0 = NaturalMI.Algebraic
                      | otherwise = NaturalMI.Automaton

        whenNonTrivial t = withProblem $ \ prob ->
          when (not $ Trs.isEmpty $ Prob.strictComponents prob) t

        wg dimension deg = Compose.composeDynamic Compose.Add $ weightgap $ (dos dimension deg)  { on = Weightgap.WgOnAny }
                     
        mx dimension deg = matrix $ dos dimension deg

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
                
        compAdd p = Compose.composeDynamic Compose.Add p
        compMul p = Compose.greedy $ Compose.composeDynamic Compose.Mult p
        compCom p = Compose.greedy $ Compose.composeDynamic Compose.Compose p        


rc2012 :: P.InstanceOf P.SomeProcessor
rc2012 = named "rc2012" $ 
          withProblem $ \ prob -> 
           case Prob.strategy prob of 
             Prob.Innermost -> some rc2012RCi
             _ -> some $ Combinators.iteProgress TOI.toInnermost rc2012RCi rc2012RC
    
  where wgOnUsable = Compose.composeDynamic Compose.Add $ 
                     weightgap defaultOptions { dim = 2
                                              , degree = (Just 1)
                                              , on = Weightgap.WgOnTrs }
          
        matchbounds = Bounds.bounds Bounds.Minimal Bounds.Match 
                      `Combinators.orFaster` Bounds.bounds Bounds.PerSymbol Bounds.Match
                      
        spopstar = PopStar.popstarSmallPS . Just                    

        dos dimension degr = defaultOptions { cbits = Just (bits' + 1)
                                            , bits = bits'
                                            , cert = cert'
                                            , dim = dim'
                                            , degree = if dim' > deg' then Just deg' else Nothing }
          where bits' | dimension <= 3 = 3
                      | otherwise = 1
                dim' = max 1 dimension
                deg' = max 0 degr
                cert' | deg' == 0 = NaturalMI.Algebraic
                      | otherwise = NaturalMI.Automaton

        wg dimension deg = Compose.composeDynamic Compose.Add $ weightgap $ (dos dimension deg)  { on = Weightgap.WgOnAny }
                     
        mx dimension deg = matrix $ dos dimension deg

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
          `Combinators.orFaster` (te (Compose.composeDynamic Compose.Add (polys 3)
                                      <||> Compose.composeDynamic Compose.Add (mx 3 3)
                                      <||> Compose.composeDynamic Compose.Add (mx 4 3)                        
                                      <||> Compose.composeDynamic Compose.Add (mx 4 4)) 
                                  >>! PopStar.popstarPS)

        directs = timeout 58 (te (compse 1) >>> te (compse 2) >>> te (compse 3) >>> te (compse 4) >>| empty)
                  `Combinators.orBetter` timeout 5 matchbounds
                  `Combinators.orBetter` timeout 58 ( bsearch "popstar" PopStar.popstarSmallPS )
                  `Combinators.orBetter` timeout 58 PopStar.popstarPS
          
          where compse i = withProblem $ \ prob ->
                  when (not $ Trs.isEmpty $ Prob.strictComponents prob) $ 
                    Compose.composeDynamic Compose.Add (spopstar i) -- binary search auf grad
                    <> (when (i == 2 || i == 3) (Compose.composeDynamic Compose.Add (polys i))
                        <||> wg i i
                        <||> Compose.composeDynamic Compose.Add (mx i i)
                        <||> when (i < 4) (Compose.composeDynamic Compose.Add (mx (i + 1) i)))
          
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
                       
          where cmp p = Compose.compose selStrictRule Compose.Add p
                selStrictRule = RS.selAnyOf (RS.selStricts `RS.selInter` RS.selRules)

        rc2012DPi = 
          toDP >>!! te (withCWDG trans) >>! basics
          where trans cwdg 
                  | cwdgDepth cwdg == (0::Int) = some $ shiftLeafs 
                  | otherwise = some $ timeout 15 shiftLeafs <> removeFirstCongruence
                removeFirstCongruence = 
                  ComposeRC.composeRC ComposeRC.composeRCselect `ComposeRC.solveBWith` proc >>> try simps
                  where proc = try simps >>> te shiftLeafs >>! basics
                cwdgDepth cwdg = maximum $ 0 : [ dp r | r <- DG.roots cwdg]
                  where dp n = maximum $ 0 : [ 1 + dp m | m <- DG.successors cwdg n]

                     

certify2012 :: P.InstanceOf P.SomeProcessor
certify2012 = some $ try IRR.irr >>| step [1..] (te . t) (const empty)
  where t d = some $ Compose.composeDynamic Compose.Add (vmx d)
                     -- <> composeDynamic Add (vps d)
        vmx dimension = matrix $ 
                        defaultOptions { cbits = Just (bits' + 1)
                                       , bits = bits'
                                       , cert = NaturalMI.Triangular
                                       , dim = dimension
                                       , useUsableArgs = False
                                       , degree = Nothing }
          where bits' | dimension <= 2 = 3
                      | dimension <= 4 = 2
                      | otherwise = 1
        -- vps 1 = poly linearPolynomial { puseUsableArgs = False }
        -- vps n = poly (customPolynomial inter) { pbits = 2
        --                                       , pcbits = Just 3
        --                                       , puseUsableArgs = False }
        --   where inter vs = [Poly.mono [(Poly.^^^) v 1 | v <- vs'] | vs' <- List.subsequences vs
        --                                            , length vs <= n]
        --                    ++ [Poly.mono [(Poly.^^^) v 2] | v <- vs] 


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
  timeout :: Int -> inp -> outp -- ^ Lifts a processor or transformation to one that times out after given number of seconds
  
instance (P.Processor p, outp ~ P.InstanceOf (S.StdProcessor (Timeout.Timeout p))) => TimesOut (P.InstanceOf p) outp  where
  timeout = Timeout.timeout

instance T.Transformer t => TimesOut (T.TheTransformer t) (T.TheTransformer (TCombinator.Timeout t)) where
  timeout = TCombinator.timeout

-- ** With Problem

class WithProblem inp outp | inp -> outp where
   withProblem :: (Problem -> inp) -> outp
   
instance T.Transformer t => WithProblem (T.TheTransformer t) (T.TheTransformer (TCombinator.WithProblem t)) where
  withProblem = TCombinator.withProblem

instance (P.Processor proc, outp ~ P.InstanceOf (S.StdProcessor (Custom.Custom Unit (P.ProofOf proc)))) => WithProblem (P.InstanceOf proc) outp where
   withProblem f = proc `S.withArgs` ()
     where proc = Custom.fromAction d (\ () prob -> P.solve (f prob) prob )
           d    = Custom.Description { Custom.as    = "Inspecting Problem..."
                                     , Custom.descr = []
                                     , Custom.args  = Unit }

withWDG :: WithProblem inp outp => (DG.DG -> inp) -> outp
withWDG f = withProblem $ \ prob -> f (DG.estimatedDependencyGraph DG.defaultApproximation prob)

withCWDG :: WithProblem inp outp => (DG.CDG -> inp) -> outp
withCWDG f = withProblem $ \ prob -> f (DG.toCongruenceGraph $ DG.estimatedDependencyGraph DG.defaultApproximation prob)


-- * Named

-- | 'named name proc' acts like 'proc', but displays itself under the name 'name' in proof outputs      
named :: P.Processor proc => String -> P.InstanceOf proc -> P.InstanceOf P.SomeProcessor
named n inst = some $ proc `S.withArgs` ()
  where proc = Custom.fromAction d (\ () -> P.solve inst)
        d    = Custom.Description { Custom.as    = n
                                  , Custom.descr = []
                                  , Custom.args  = Unit }
