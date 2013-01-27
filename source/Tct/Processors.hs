--------------------------------------------------------------------------------
-- | 
-- Module      :  Tct.Processors
-- Copyright   :  (c) Martin Avanzini <martin.avanzini@uibk.ac.at>, 
--                Georg Moser <georg.moser@uibk.ac.at>, 
--                Andreas Schnabl <andreas.schnabl@uibk.ac.at>
-- License     :  LGPL (see COPYING)
--
-- Maintainer  :  Martin Avanzini <martin.avanzini@uibk.ac.at>
-- Stability   :  unstable
-- Portability :  unportable      
-- 
-- This module collects available /processors/ of TcT.
-- A processor 'p' is the TcT representation of a complexity techniques
-- that, given a complexity problem, constructs a complete proof for 
-- the problem. 
-- Processors are parameterised in some arguments that control the behaviour
-- of the processor, for instance, the matrix processor is parameterised 
-- in the dimension of the constructed matrix interpretation. 
-- Parameterised processors are called /processor instances/, and 
-- can be obtained using the constructors in "Tct.Instances".
--
-- A list of processors and their synopsis can also be obtained from
-- the command line, using the flag @--list@.
--------------------------------------------------------------------------------   
{-# LANGUAGE CPP #-}
module Tct.Processors where

-- Use 'tct-utils/scripts/createProcessors.sh <tct-source-dir>' to create
-- list of processors

import Prelude hiding (fail, uncurry)

import qualified Tct.Processor as P
import qualified Tct.Processor.Standard as S
import Tct.Processor.Standard (StdProcessor)
import qualified Tct.Processor.Transformations as T
import qualified Tct.Method.Predicates as Preds
import Tct.Method.Predicates hiding
  ( isDuplicating
   , isConstructor 
   , isGround
   , isLeftLinear
   , isRightLinear
   , isWellFormed
   , isOutermost
   , isCollapsing
   , isInnermost
   , isFull
   , isContextSensitive
   , isDCProblem
   , isRCProblem) 
import Tct.Method.Bounds hiding (bounds)
import Tct.Method.Combinator hiding (fail, success, empty, open, ite, best, fastest, sequentially)
import Tct.Method.Compose hiding (compose)
import Tct.Method.ComposeRC hiding (composeRC)
import Tct.Method.DP.DependencyPairs hiding (dependencyPairs)
import Tct.Method.DP.PathAnalysis hiding (pathAnalysis)
import Tct.Method.DP.Simplification hiding (simpDPRHS, simpPE)
import Tct.Method.DP.UsableRules hiding (usableRules)
import Tct.Method.EpoStar hiding (epostar)
import Tct.Method.InnermostRuleRemoval hiding (irr)
import Tct.Method.ToInnermost hiding (toInnermost)
import Tct.Method.Matrix.ArcticMI hiding (arctic)
import Tct.Method.Matrix.NaturalMI
import Tct.Method.Poly.NaturalPI
import Tct.Method.PopStar hiding (popstar, lmpo)
import Tct.Method.Uncurry hiding (uncurry)
import Tct.Method.Weightgap
import Tct.Method.Timeout hiding (timeout)
import Tct.Method.Mpo hiding (mpo)
import qualified Tct.Instances as Inst
import Tct.Method.Custom (Custom (..))
import qualified Tct.Processor.Args as A

-- generated: Fri Jan  6 13:08:14 JST 2012
builtInProcessors :: P.AnyProcessor 
builtInProcessors = 
    isDuplicating
    P.<|>
    isConstructor
    P.<|>
    isCollapsing
    P.<|>
    isGround
    P.<|>
    isLeftLinear
    P.<|>
    isRightLinear
    P.<|>
    isWellFormed
    P.<|>
    isOutermost
    P.<|>
    isInnermost
    P.<|>
    isFull
    P.<|>
    isContextSensitive
    P.<|>
    isDCProblem
    P.<|>
    isRCProblem
    P.<|>
    popstar
    P.<|>
    ppopstar
    P.<|>
    lmpo
    P.<|>
    bounds
    P.<|>
    fail
    P.<|>
    success
    P.<|>
    empty
    P.<|>
    open
    P.<|>
    ite
    P.<|>
    best
    P.<|>
    fastest
    P.<|>
    sequentially
    P.<|>
    epostar
    P.<|>
    matrix
    P.<|>
    arctic
    P.<|>
    mpo
    P.<|>
    poly
    P.<|>
    timeout
    P.<|> 
    weightgap
    P.<|>
    S.StdProcessor irr
    P.<|>
    S.StdProcessor toInnermost
    P.<|>
    S.StdProcessor composeRC
    P.<|>
    S.StdProcessor compose
    P.<|>
    S.StdProcessor dependencyPairs
    P.<|>
    S.StdProcessor removeTail
    P.<|>
    S.StdProcessor removeHead
    P.<|>
    S.StdProcessor simpDPRHS
    P.<|>
    S.StdProcessor simpPE
    P.<|>
    -- S.StdProcessor inline
    -- P.<|>
    S.StdProcessor usableRules
    P.<|>
    S.StdProcessor pathAnalysis
    P.<|>
    S.StdProcessor uncurry
    P.<|>
    Custom { as = "rc2012", code =  Inst.rc2012, arguments = A.Unit }
    P.<|>
    Custom { as = "dc2012", code =  Inst.dc2012, arguments = A.Unit }
    P.<|>
    Custom { as = "certify2012", code =  Inst.certify2012, arguments = A.Unit }    
    P.<|>
    Custom { as = "rc2011", code =  Inst.rc2012, arguments = A.Unit }    
    P.<|>
    Custom { as = "dc2011", code =  Inst.rc2012, arguments = A.Unit }    
    P.<|>
    foldr (P.<|>) P.none Preds.predicateProcessors

-- generated: Fri Jan  6 13:10:41 JST 2012
{- |

[on :: strict|weak|both|union /(optional)/] Chooses the TRS from the problem on which the predicate is applied (only applies to predicates on TRSs).


-}
isDuplicating :: S.StdProcessor Predicate
isDuplicating = isDuplicatingProcessor

{- |

[on :: strict|weak|both|union /(optional)/] Chooses the TRS from the problem on which the predicate is applied (only applies to predicates on TRSs).


-}
isConstructor :: S.StdProcessor Predicate
isConstructor = isConstructorProcessor

{- |

[on :: strict|weak|both|union /(optional)/] Chooses the TRS from the problem on which the predicate is applied (only applies to predicates on TRSs).


-}
isCollapsing :: S.StdProcessor Predicate
isCollapsing = isCollapsingProcessor

{- |

[on :: strict|weak|both|union /(optional)/] Chooses the TRS from the problem on which the predicate is applied (only applies to predicates on TRSs).


-}
isGround :: S.StdProcessor Predicate
isGround = isGroundProcessor

{- |

[on :: strict|weak|both|union /(optional)/] Chooses the TRS from the problem on which the predicate is applied (only applies to predicates on TRSs).


-}
isLeftLinear :: S.StdProcessor Predicate
isLeftLinear = isLeftLinearProcessor

{- |

[on :: strict|weak|both|union /(optional)/] Chooses the TRS from the problem on which the predicate is applied (only applies to predicates on TRSs).


-}
isRightLinear :: S.StdProcessor Predicate
isRightLinear = isRightLinearProcessor

{- |

[on :: strict|weak|both|union /(optional)/] Chooses the TRS from the problem on which the predicate is applied (only applies to predicates on TRSs).


-}
isWellFormed :: S.StdProcessor Predicate
isWellFormed = isWellFormedProcessor

{- |

[on :: strict|weak|both|union /(optional)/] Chooses the TRS from the problem on which the predicate is applied (only applies to predicates on TRSs).


-}
isOutermost :: S.StdProcessor Predicate
isOutermost = isOutermostProcessor

{- |

[on :: strict|weak|both|union /(optional)/] Chooses the TRS from the problem on which the predicate is applied (only applies to predicates on TRSs).


-}
isInnermost :: S.StdProcessor Predicate
isInnermost = isInnermostProcessor

{- |

[on :: strict|weak|both|union /(optional)/] Chooses the TRS from the problem on which the predicate is applied (only applies to predicates on TRSs).


-}
isFull :: S.StdProcessor Predicate
isFull = isFullProcessor

{- |

[on :: strict|weak|both|union /(optional)/] Chooses the TRS from the problem on which the predicate is applied (only applies to predicates on TRSs).


-}
isContextSensitive :: S.StdProcessor Predicate
isContextSensitive = isContextSensitiveProcessor

{- |

[on :: strict|weak|both|union /(optional)/] Chooses the TRS from the problem on which the predicate is applied (only applies to predicates on TRSs).


-}
isDCProblem :: S.StdProcessor Predicate
isDCProblem = isDCProblemProcessor

{- |

[on :: strict|weak|both|union /(optional)/] Chooses the TRS from the problem on which the predicate is applied (only applies to predicates on TRSs).


-}
isRCProblem :: S.StdProcessor Predicate
isRCProblem = isRCProblemProcessor

{- |
This processor implements orientation of the input problem using
\'polynomial path orders\',
a technique applicable for innermost runtime-complexity analysis.
Polynomial path orders are a miniaturisation of \'multiset path
orders\',
restricted so that compatibility assesses a polynomial bound on the
innermost runtime-complexity.
The implementation for DP problems additionally employs argument
filterings.

[ps :: On|Off /(optional)/] Parameter substitution: If enabled, parameter substitution is allowed, strengthening the order.

[wsc :: On|Off /(optional)/] Weak Safe Composition: If enabled then composition is restricted to weak safe composition.

[deg :: \<nat>|none /(optional)/] Deg: If set and applicable, polynomially bounded runtime complexity with given degree is proven. This flag only works in combination with product extension and weak safe composition,  cf. 'popstarSmall'.

-}

popstar :: S.StdProcessor PopStar
popstar = popstarProcessor

{- |
This processor implements orientation of the input problem using
\'polynomial path orders\'
with product extension, c.f. processor \'popstar\'.

[ps :: On|Off /(optional)/] Parameter substitution: If enabled, parameter substitution is allowed, strengthening the order.

[wsc :: On|Off /(optional)/] Weak Safe Composition: If enabled then composition is restricted to weak safe composition.

[deg :: \<nat>|none /(optional)/] Deg: If set and applicable, polynomially bounded runtime complexity with given degree is proven. This flag only works in combination with product extension and weak safe composition,  cf. 'popstarSmall'.

-}
ppopstar :: S.StdProcessor PopStar
ppopstar = ppopstarProcessor

{- |
This processor implements orientation of the input problem using
\'light multiset path orders\',
a technique applicable for innermost runtime-complexity analysis.
Light multiset path orders are a miniaturisation of \'multiset path
orders\',
restricted so that compatibility assesses polytime computability of
the functions defined.
Further, it induces exponentially bounded innermost
runtime-complexity.

[ps :: On|Off /(optional)/] Parameter substitution: If enabled, parameter substitution is allowed, strengthening the order.

[wsc :: On|Off /(optional)/] Weak Safe Composition: If enabled then composition is restricted to weak safe composition.

[deg :: \<nat>|none /(optional)/] Deg: If set and applicable, polynomially bounded runtime complexity with given degree is proven. This flag only works in combination with product extension and weak safe composition,  cf. 'popstarSmall'.

-}
lmpo :: S.StdProcessor PopStar
lmpo = lmpoProcessor

{- |
This processor implements the (match|roof|top)-bounds technique
that induces linear derivational- and runtime-complexity for
right-linear problems.
For non-right-linear problems this processor fails immediately.

[initial :: minimal|perSymbol /(optional)/] The employed initial automaton.
If 'perSymbol' is set then the initial automaton admits one dedicated
state per function symbols.
If 'minimal' is set then the initial automaton admits exactly
one state for derivational-complexity analysis. For runtime-complexity analysis, 
two states are used in order to distinguish defined symbols from constructors.


[enrichment :: match|roof|top /(optional)/] The employed enrichment.

-}
bounds :: S.StdProcessor Bounds
bounds = boundsProcessor

{- |
Processor \'fail\' always returns the answer \'No\'.

-}
fail :: S.StdProcessor Fail
fail = failProcessor

{- |
Processor \'success\' always returns the answer \'Yes(?,?)\'.

-}
success :: S.StdProcessor Success
success = successProcessor

{- |
Processor \'empty\' returns \'Yes(O(1),O(1))\' if the strict
component of the problem is empty.

-}
empty :: S.StdProcessor EmptyRules
empty = emptyProcessor

{- |

-}
open :: S.StdProcessor Open
open = openProcessor

{- |
This processor implements conditional branching

[guard :: \<processor>] The guard processor. It succeeds if it returns 'Yes(*,*)'.

[then :: \<processor>] The processor that is applied if guard succeeds.

[else :: \<processor>] The processor that is applied if guard fails.

-}
ite :: S.StdProcessor (Ite P.AnyProcessor P.AnyProcessor P.AnyProcessor)
ite = iteProcessor

{- |
Processor \'Best\' applies the given list of processors in parallel
and returns the proof admitting the lowest complexity certificate.

[subprocessors :: \<processor>...] a list of subprocessors

-}
best :: S.StdProcessor (OneOf P.AnyProcessor)
best = bestProcessor

{- |
Processor \'Fastest\' applies the given list of processors in
parallel and returns the first successful proof.

[subprocessors :: \<processor>...] a list of subprocessors

-}
fastest :: S.StdProcessor (OneOf P.AnyProcessor)
fastest = fastestProcessor

{- |
Processor \'Sequentially\' applies the given list of processors
sequentially and returns the first successful proof.

[subprocessors :: \<processor>...] a list of subprocessors

-}
sequentially :: S.StdProcessor (OneOf P.AnyProcessor)
sequentially = sequentiallyProcessor

{- |
This processor implements orientation of the input problem using
\'exponential path orders\', a technique applicable for innermost
runtime-complexity analysis. Exponential path orders are a
miniaturisation of \'lexicographic path orders\', restricted so
that compatibility assesses exponential runtime complexity.

[ecomp :: On|Off /(optional)/] Extended Composition: If this flag is enabled, then the slightly more . liberal composition scheme 'f(x;y) = h(g(;x);k(x;y))' is permitted. Currently it is not known whether this extension is sound.

-}
epostar :: S.StdProcessor EpoStar
epostar = epostarProcessor

{- |
This processor orients the problem using matrix-interpretation over
natural numbers.

[cert :: algebraic|automaton|nothing /(optional)/] This argument specifies restrictions on the matrix-interpretation which induce polynomial growth of
the interpretation of the considered starting terms relative to their size.
Here 'algebraic' refers to simple algebraic restrictions on matrices (in the current implementation,
they are simply restricted to triangular shape, i.e. matrices where coefficients in the lower-left
half below the diagonal are zero. Such matrix-interpretations induce polynomial derivational-complexity.
If 'automaton' is given as argument, then criteria from the theory of weighted automata are used instead
(in the current implementation, the negations of the criteria EDA, and possibly IDA(n), in the case that
the flag 'degree' is set, are used).
If 'nothing' is given, then matrix-interpretations of all function symbols are unrestricted.
Note that matrix interpretations produced with this option do not induce polynomial complexities in general.
The default value is 'automaton'.


[degree :: \<nat>|none /(optional)/] This argument ensures that the complexity induced by the searched matrix interpretation is bounded by a
polynomial of the given degree. Its internal effect is dictated by the value the argument 'cert' is set to.
If it is set to 'algebraic', this restricts the number of non-zero entries in the diagonals of the matrices.
If it is set to 'automaton', this set the paramter 'n' in the criterion 'not IDA(n)'.
Finally, if it is set to 'unrestricted', the effect of setting the 'degree' argument is unspecified.


[dim :: \<nat> /(optional)/] This argument specifies the dimension of the vectors and square-matrices appearing
 in the matrix-interpretation.


[bound :: \<nat> /(optional)/] This argument specifies an upper-bound on coefficients appearing in the interpretation.
Such an upper-bound is necessary as we employ bit-blasting to SAT internally
when searching for compatible matrix interpretations.


[bits :: \<nat>|none /(optional)/] This argument plays the same role as 'bound',
but instead of an upper-bound the number of bits is specified.
This argument overrides the argument 'bound'.


[cbits :: \<nat>|none /(optional)/] This argument specifies the number of bits used for intermediate results, 
as for instance coefficients of matrices obtained by interpreting
left- and right-hand sides.


[uargs :: On|Off /(optional)/] This argument specifies whether usable arguments are computed (if applicable)
in order to relax the monotonicity constraints on the interpretation.


-}
matrix :: S.StdProcessor NaturalMI
matrix = matrixProcessor

{- |
This processor orients the problem using matrix-interpretation over
the arctic semiring.

[dim :: \<nat> /(optional)/] This argument specifies the dimension of the vectors and square-matrices appearing
 in the matrix-interpretation.


[bound :: \<nat> /(optional)/] This argument specifies an upper-bound on coefficients appearing in the interpretation.
Such an upper-bound is necessary as we employ bit-blasting to SAT internally
when searching for compatible matrix interpretations.


[bits :: \<nat>|none /(optional)/] This argument plays the same role as 'bound',
but instead of an upper-bound the number of bits is specified.
This argument overrides the argument 'bound'.


[cbits :: \<nat>|none /(optional)/] This argument specifies the number of bits used for intermediate results, 
as for instance coefficients of matrices obtained by interpreting
left- and right-hand sides.


[uargs :: On|Off /(optional)/] This argument specifies whether usable arguments are computed (if applicable)
in order to relax the monotonicity constraints on the interpretation.


-}
arctic :: S.StdProcessor ArcticMI
arctic = arcticProcessor

{- |
This processor implements \'multiset path orders\' as found in the
literature.

-}
mpo :: StdProcessor Mpo
mpo = mpoProcessor

{- |
This processor orients the problem using polynomial interpretation
over natural numbers.

[kind :: linear|stronglylinear|simple|simplemixed|quadratic /(optional)/] This argument specifies the shape of the polynomials used in the interpretation.
Allowed values are 'stronglylinear', 'linear', 'simple', 'simplemixed', and 'quadratic',
referring to the respective shapes of the abstract polynomials used.
The deault value is 'stronglylinear'.


[bound :: \<nat> /(optional)/] This argument specifies an upper-bound on coefficients appearing in the interpretation.
Such an upper-bound is necessary as we employ bit-blasting to SAT internally
when searching for compatible matrix interpretations.


[bits :: \<nat>|none /(optional)/] This argument plays the same role as 'bound',
but instead of an upper-bound the number of bits is specified.
This argument overrides the argument 'bound'.


[cbits :: \<nat>|none /(optional)/] This argument specifies the number of bits used for intermediate results, 
as for instance coefficients of matrices obtained by interpreting
left- and right-hand sides.


[uargs :: On|Off /(optional)/] This argument specifies whether usable arguments are computed (if applicable)
in order to relax the monotonicity constraints on the interpretation.


-}
poly :: S.StdProcessor NaturalPI
poly = polyProcessor

{- |
The processor either returns the result of the given processor
or, if the timeout elapses, aborts the computation and returns
MAYBE.

[timeout :: \<nat>] The timeout in seconds

[processor :: \<processor>] The processor to apply with timeout

-}
timeout :: S.StdProcessor (Timeout P.AnyProcessor)
timeout = timeoutProcessor

{- |
This processor removes rules \'f(l_1,...,l_n) -> r\' for which l_i
(1 \<= i \<=n) is not a normal form.
The processor applies only to innermost problems.

[subprocessor :: \<processor>] The processor that is applied on the transformed problem(s)

[strict :: On|Off /(optional)/] If this flag is set and the transformation fails, this processor aborts.
Otherwise, it applies the subprocessor on the untransformed input.


[parallel :: On|Off /(optional)/] Decides whether the given subprocessor should be applied in parallel.

[checkSubsumed :: On|Off /(optional)/] This flag determines whether the processor should reuse proofs in case that one generated problem subsumes another one.
A problem (A) is subsumed by problem (B) if the complexity of (A) is bounded from above by the complexity of (B).
Currently we only take subset-inclusions of the different components into account.


-}
irr :: T.Transformation InnermostRuleRemoval P.AnyProcessor
irr = irrProcessor

{- |
This processor implements processor \'compose\' specifically for
the (weak) dependency pair setting. It tries to estimate the
complexity of the input problem based on the complexity of
dependency pairs of upper congruence classes (with respect to the
congruence graph) relative to the dependency pairs in the remaining
lower congruence classes. The overall upper bound for the
complexity of the input problem is estimated by multiplication of
upper bounds of the sub problems.
Note that the processor allows the optional specification of
processors that are applied on the two individual subproblems. The
transformation results into the systems which could not be oriented
by those processors.

[subprocessor :: \<processor>] The processor that is applied on the transformed problem(s)

[strict :: On|Off /(optional)/] If this flag is set and the transformation fails, this processor aborts.
Otherwise, it applies the subprocessor on the untransformed input.


[parallel :: On|Off /(optional)/] Decides whether the given subprocessor should be applied in parallel.

[checkSubsumed :: On|Off /(optional)/] This flag determines whether the processor should reuse proofs in case that one generated problem subsumes another one.
A problem (A) is subsumed by problem (B) if the complexity of (A) is bounded from above by the complexity of (B).
Currently we only take subset-inclusions of the different components into account.


[split ::  /(optional)/] This problem determines the strict rules of the selected upper congruence rules.

[sub-processor-A :: \<processor>|none /(optional)/] If given, applied on the problem reflecting the upper congruence classes.

[sub-processor-B :: \<processor>|none /(optional)/] If given, applied on the problem reflecting the lower congruence classes.

-}
composeRC :: T.Transformation (ComposeRC P.AnyProcessor P.AnyProcessor) P.AnyProcessor
composeRC = composeRCProcessor

{- |
Uses the weight gap principle to shift some strict rules to the
weak part of the problem.

[subprocessor :: \<processor>] The processor that is applied on the transformed problem(s)

[strict :: On|Off /(optional)/] If this flag is set and the transformation fails, this processor aborts.
Otherwise, it applies the subprocessor on the untransformed input.


[parallel :: On|Off /(optional)/] Decides whether the given subprocessor should be applied in parallel.

[checkSubsumed :: On|Off /(optional)/] This flag determines whether the processor should reuse proofs in case that one generated problem subsumes another one.
A problem (A) is subsumed by problem (B) if the complexity of (A) is bounded from above by the complexity of (B).
Currently we only take subset-inclusions of the different components into account.


[on :: trs|any /(optional)/] This flag determine which rules have to be strictly oriented by the the matrix interpretation for
the weight gap principle. Here 'trs' refers to all strict non-dependency-pair rules of the
considered problem, while 'any' only demands any rule at all to be strictly oriented.
The default value is 'trs'.


[cert :: algebraic|automaton|nothing /(optional)/] This argument specifies restrictions on the matrix-interpretation for the weight gap condition which induce polynomial growth of
the interpretation of the considered starting terms relative to their size.
Here 'algebraic' refers to simple algebraic restrictions on matrices (in the current implementation,
they are simply restricted to triangular shape, i.e. matrices where coefficients in the lower-left
half below the diagonal are zero. Such matrix-interpretations induce polynomial derivational-complexity.
If 'automaton' is given as argument, then criteria from the theory of weighted automata are used instead
(in the current implementation, the negations of the criteria EDA, and possibly IDA(n), in the case that
the flag 'degree' is set, are used).
If 'nothing' is given, then matrix-interpretations of all function symbols are unrestricted.
Note that matrix interpretations produced with this option do not induce polynomial complexities in general.
The default value is 'automaton'.


[degree :: \<nat>|none /(optional)/] This argument ensures that the complexity induced by the searched matrix interpretation for the weight gap condition is bounded by a
polynomial of the given degree. Its internal effect is dictated by the value the argument 'cert' is set to.
If it is set to 'algebraic', this restricts the number of non-zero entries in the diagonals of the matrices.
If it is set to 'automaton', this set the paramter 'n' in the criterion 'not IDA(n)'.
Finally, if it is set to 'unrestricted', the effect of setting the 'degree' argument is unspecified.


[dim :: \<nat> /(optional)/] This argument specifies the dimension of the vectors and square-matrices appearing
 in the matrix-interpretation for the weight gap condition.


[bound :: \<nat> /(optional)/] This argument specifies an upper-bound on coefficients appearing in the interpretation.
Such an upper-bound is necessary as we employ bit-blasting to SAT internally
when searching for compatible matrix interpretations for the weight gap condition.


[bits :: \<nat>|none /(optional)/] This argument plays the same role as 'bound',
but instead of an upper-bound the number of bits is specified.
This argument overrides the argument 'bound'.


[cbits :: \<nat>|none /(optional)/] This argument specifies the number of bits used for intermediate results,
computed for the matrix interpretation of the weight gap condition.


[uargs :: On|Off /(optional)/] This argument specifies whether usable arguments are computed (if applicable)
in order to relax the monotonicity constraints on the interpretation.


-}
weightgap :: S.StdProcessor WeightGap
weightgap = S.StdProcessor WeightGap

{- |
This transformation implements techniques for splitting the
complexity problem into two complexity problems (A) and (B) so that
the complexity of the input problem can be estimated by the
complexity of the transformed problem. The processor closely
follows the ideas presented in \/Complexity Bounds From Relative
Termination Proofs\/
(\<http:\/\/www.imn.htwk-leipzig.de\/~waldmann\/talk\/06\/rpt\/rel\/main.pdf>)

[subprocessor :: \<processor>] The processor applied on subproblem (A).


[subprocessor :: \<processor>] The processor that is applied on the transformed problem(s)

[strict :: On|Off /(optional)/] If this flag is set and the transformation fails, this processor aborts.
Otherwise, it applies the subprocessor on the untransformed input.


[parallel :: On|Off /(optional)/] Decides whether the given subprocessor should be applied in parallel.

[checkSubsumed :: On|Off /(optional)/] This flag determines whether the processor should reuse proofs in case that one generated problem subsumes another one.
A problem (A) is subsumed by problem (B) if the complexity of (A) is bounded from above by the complexity of (B).
Currently we only take subset-inclusions of the different components into account.


[split :: dynamic /(optional)/] This argument of type 'Compose.Partitioning' determines strict rules of problem (A). Usually, this should be set to 'Dynamic', in which case the given processor determines selection of rules dynamically.

[allow :: Add|Mult|Compose /(optional)/] This argument type 'Compose.ComposeBound' determines how the complexity certificate should be obtained from subproblems (A) and (B). Consequently, this argument also determines the shape of (B). The third argument defines a processor that is applied on problem (A). If this processor succeeds, the input problem is transformed into (B). Note that for compose bound 'Mult' the transformation only succeeds if applied to non size-increasing Problems.

-}
compose :: T.Transformation (Compose P.AnyProcessor) P.AnyProcessor
compose = composeProcessor

{- |
Switches to innermost rewriting on overlay and right-linear input.

[subprocessor :: \<processor>] The processor that is applied on the transformed problem(s)

[strict :: On|Off /(optional)/] If this flag is set and the transformation fails, this processor aborts.
Otherwise, it applies the subprocessor on the untransformed input.


[parallel :: On|Off /(optional)/] Decides whether the given subprocessor should be applied in parallel.

[checkSubsumed :: On|Off /(optional)/] This flag determines whether the processor should reuse proofs in case that one generated problem subsumes another one.
A problem (A) is subsumed by problem (B) if the complexity of (A) is bounded from above by the complexity of (B).
Currently we only take subset-inclusions of the different components into account.


-}
toInnermost :: T.Transformation ToInnermost P.AnyProcessor
toInnermost = toInnermostProcessor

{- |
Applies the (weak) depencency pair transformation.

[subprocessor :: \<processor>] The processor that is applied on the transformed problem(s)

[strict :: On|Off /(optional)/] If this flag is set and the transformation fails, this processor aborts.
Otherwise, it applies the subprocessor on the untransformed input.


[parallel :: On|Off /(optional)/] Decides whether the given subprocessor should be applied in parallel.

[checkSubsumed :: On|Off /(optional)/] This flag determines whether the processor should reuse proofs in case that one generated problem subsumes another one.
A problem (A) is subsumed by problem (B) if the complexity of (A) is bounded from above by the complexity of (B).
Currently we only take subset-inclusions of the different components into account.


[usetuples :: On|Off /(optional)/] This argument specifies whether dependency tuples instead of pairs should be used.


-}


dependencyPairs :: T.Transformation DPs P.AnyProcessor
dependencyPairs = dependencyPairsProcessor

{- |
Recursively removes all nodes that are either leafs in the
dependency-graph or from the given problem. Only applicable if the
strict component is empty.

[subprocessor :: \<processor>] The processor that is applied on the transformed problem(s)

[strict :: On|Off /(optional)/] If this flag is set and the transformation fails, this processor aborts.
Otherwise, it applies the subprocessor on the untransformed input.


[parallel :: On|Off /(optional)/] Decides whether the given subprocessor should be applied in parallel.

[checkSubsumed :: On|Off /(optional)/] This flag determines whether the processor should reuse proofs in case that one generated problem subsumes another one.
A problem (A) is subsumed by problem (B) if the complexity of (A) is bounded from above by the complexity of (B).
Currently we only take subset-inclusions of the different components into account.


-}

removeHead :: T.Transformation RemoveHead P.AnyProcessor
removeHead = removeHeadProcessor


removeTail :: T.Transformation RemoveTail P.AnyProcessor
removeTail = removeTailProcessor

{- |
Simplify right hand sides of dependency pairs by removing marked
subterms whose root symbols are undefined. Only applicable if the
strict component is empty.

[subprocessor :: \<processor>] The processor that is applied on the transformed problem(s)

[strict :: On|Off /(optional)/] If this flag is set and the transformation fails, this processor aborts.
Otherwise, it applies the subprocessor on the untransformed input.


[parallel :: On|Off /(optional)/] Decides whether the given subprocessor should be applied in parallel.

[checkSubsumed :: On|Off /(optional)/] This flag determines whether the processor should reuse proofs in case that one generated problem subsumes another one.
A problem (A) is subsumed by problem (B) if the complexity of (A) is bounded from above by the complexity of (B).
Currently we only take subset-inclusions of the different components into account.


-}
simpDPRHS :: T.Transformation SimpRHS P.AnyProcessor
simpDPRHS = simpDPRHSProcessor

{- |
Moves a strict dependency into the weak component if all
predecessors in the dependency graph are strict and there is no
edge from the rule to itself. Only 

[subprocessor :: \<processor>] The processor that is applied on the transformed problem(s)

[strict :: On|Off /(optional)/] If this flag is set and the transformation fails, this processor aborts.
Otherwise, it applies the subprocessor on the untransformed input.


[parallel :: On|Off /(optional)/] Decides whether the given subprocessor should be applied in parallel.

[checkSubsumed :: On|Off /(optional)/] This flag determines whether the processor should reuse proofs in case that one generated problem subsumes another one.
A problem (A) is subsumed by problem (B) if the complexity of (A) is bounded from above by the complexity of (B).
Currently we only take subset-inclusions of the different components into account.


-}
-- inline :: T.Transformation Inline P.AnyProcessor
-- inline = inlineProcessor

simpPE :: T.Transformation (SimpPE P.AnyProcessor) P.AnyProcessor
simpPE = simpPEProcessor

{- |
This processor restricts the strict- and weak-rules to usable rules
with
respect to the dependency pairs.

[subprocessor :: \<processor>] The processor that is applied on the transformed problem(s)

[strict :: On|Off /(optional)/] If this flag is set and the transformation fails, this processor aborts.
Otherwise, it applies the subprocessor on the untransformed input.


[parallel :: On|Off /(optional)/] Decides whether the given subprocessor should be applied in parallel.

[checkSubsumed :: On|Off /(optional)/] This flag determines whether the processor should reuse proofs in case that one generated problem subsumes another one.
A problem (A) is subsumed by problem (B) if the complexity of (A) is bounded from above by the complexity of (B).
Currently we only take subset-inclusions of the different components into account.


-}
usableRules :: T.Transformation UR P.AnyProcessor
usableRules = usableRulesProcessor

{- |
This processor implements path-analysis as described in the
dependency pair paper.

[subprocessor :: \<processor>] The processor that is applied on the transformed problem(s)

[strict :: On|Off /(optional)/] If this flag is set and the transformation fails, this processor aborts.
Otherwise, it applies the subprocessor on the untransformed input.


[parallel :: On|Off /(optional)/] Decides whether the given subprocessor should be applied in parallel.

[checkSubsumed :: On|Off /(optional)/] This flag determines whether the processor should reuse proofs in case that one generated problem subsumes another one.
A problem (A) is subsumed by problem (B) if the complexity of (A) is bounded from above by the complexity of (B).
Currently we only take subset-inclusions of the different components into account.


-}
pathAnalysis :: T.Transformation PathAnalysis P.AnyProcessor
pathAnalysis = pathAnalysisProcessor

{- |
This processor implements \'Uncurrying\' for
left-head-variable-free ATRSs

[subprocessor :: \<processor>] The processor that is applied on the transformed problem(s)

[strict :: On|Off /(optional)/] If this flag is set and the transformation fails, this processor aborts.
Otherwise, it applies the subprocessor on the untransformed input.


[parallel :: On|Off /(optional)/] Decides whether the given subprocessor should be applied in parallel.

[checkSubsumed :: On|Off /(optional)/] This flag determines whether the processor should reuse proofs in case that one generated problem subsumes another one.
A problem (A) is subsumed by problem (B) if the complexity of (A) is bounded from above by the complexity of (B).
Currently we only take subset-inclusions of the different components into account.


-}
uncurry :: T.Transformation Uncurry P.AnyProcessor
uncurry = uncurryProcessor

