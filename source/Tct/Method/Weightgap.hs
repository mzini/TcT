{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

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

module Tct.Method.Weightgap where

import Prelude hiding ((&&), (||))
import Text.PrettyPrint.HughesPJ hiding (empty)
import Data.Typeable
import qualified Data.Map as Map
import qualified Data.Set as Set

import Qlogic.Boolean
import Qlogic.Diophantine hiding (add)
import Qlogic.Semiring
import qualified Qlogic.NatSat as N

import Termlib.Problem (Problem(..))
import Termlib.Rule (Rule(..))
import Termlib.Trs (Trs(..))
import Termlib.Utils
import qualified Termlib.FunctionSymbol as F
import qualified Termlib.Problem as Prob
import qualified Termlib.Rule as R
import qualified Termlib.Trs as Trs

import Tct.Certificate (add, certified, unknown, upperBound)
import Tct.Encoding.AbstractInterpretation
import Tct.Encoding.Matrix
import Tct.Encoding.UsablePositions
import Tct.Processor.Args
import Tct.Processor.Args.Instances
import Tct.Processor.Orderings
import Tct.Processor.PPrint (enumeration', indent)
import Tct.Method.Matrix.MatrixInterpretation hiding (signature)
import Tct.Method.Matrix.NaturalMI
import qualified Tct.Processor.Args as A
import qualified Tct.Processor as P
import qualified Tct.Processor.Standard as S
import qualified Tct.Processor.Transformations as T

data WeightGap = WeightGap

data WgOn = WgOnTrs
          | WgOnAny
            deriving (Typeable, Bounded, Enum)

instance Show WgOn where
  show WgOnTrs = "trs"
  show WgOnAny = "any"

data WeightGapProof = WeightGapProof { wgInputProblem :: Problem
                                     , wgProof :: OrientationProof MatrixOrder
                                     , wgRemovableDps :: [Rule]
                                     , wgRemovableTrs :: [Rule]
                                     }

instance PrettyPrintable WeightGapProof where
  pprint wgp = text (if P.succeeded p
                     then "The weightgap principle applies, using the following adequate RMI:"
                     else "The weight gap principle does not apply:")
               $+$ indent (pprint p)
               $+$ text "The following dependency pairs were strictly oriented:"
               $+$ text ""
               $+$ nest 2 (pprint (Trs.fromRules $ wgRemovableDps wgp, signature ip, variables ip))
               $+$ text "The following rules were strictly oriented:"
               $+$ text ""
               $+$ nest 2 (pprint (Trs.fromRules $ wgRemovableTrs wgp, signature ip, variables ip))
               $+$ text "Above strict rules are moved into the weak component."
    where ip = wgInputProblem wgp
          p  = wgProof wgp

instance T.TransformationProof WeightGap where 
  answer proof = case T.subProofs proof of 
                     [(_,subproof)] -> mkAnswer (P.answer wgproof) (P.answer subproof)
                     _              -> P.MaybeAnswer
    where wgproof = wgProof $ T.transformationProof proof
          mkAnswer (P.CertAnswer tc) (P.CertAnswer c) = P.CertAnswer $ certified (unknown, add (upperBound tc) (upperBound c))
          mkAnswer (P.CertAnswer _ ) a                = a
          mkAnswer _                 _                = error "Tct.Method.Weightgap.answer: unexpected pattern amtching case"
                       
  pprintProof _ _  = pprint 


instance T.Transformer WeightGap where
  name WeightGap = "weightgap"
  description WeightGap = [ "Uses the weight gap principle to shift some strict rules to the weak part of the problem." ]

  type T.ArgumentsOf WeightGap = (Arg (EnumOf WgOn)) :+: (Arg (EnumOf NaturalMIKind)) :+: (Arg (Maybe Nat)) :+: (Arg Nat) :+: (Arg Nat)  :+: (Arg (Maybe Nat))  :+: (Arg (Maybe Nat)) :+: (Arg Bool)
  type T.ProofOf WeightGap = WeightGapProof
  arguments WeightGap =   opt { A.name        = "on"
                              , A.description = unlines [ "This flag determine which rules have to be strictly oriented by the the matrix interpretation for"
                                                        , "the weight gap principle. Here 'trs' refers to all strict non-dependency-pair rules of the"
                                                        , "considered problem, while 'any' only demands any rule at all to be strictly oriented."
                                                        , "The default value is 'trs'."
                                                        ]
                              , A.defaultValue = WgOnTrs}
                          :+:
                          opt { A.name        = "cert"
                              , A.description = unlines [ "This argument specifies restrictions on the matrix-interpretation for the weight gap condition which induce polynomial growth of"
                                                        , "the interpretation of the considered starting terms relative to their size."
                                                        , "Here 'algebraic' refers to simple algebraic restrictions on matrices (in the current implementation,"
                                                        , "they are simply restricted to triangular shape, i.e. matrices where coefficients in the lower-left"
                                                        , "half below the diagonal are zero. Such matrix-interpretations induce polynomial derivational-complexity." 
                                                        , "If 'automaton' is given as argument, then criteria from the theory of weighted automata are used instead"
                                                        , "(in the current implementation, the negations of the criteria EDA, and possibly IDA(n), in the case that"
                                                        , "the flag 'degree' is set, are used)."
                                                        , "If 'nothing' is given, then matrix-interpretations of all function symbols are unrestricted."
                                                        , "Note that matrix interpretations produced with this option do not induce polynomial complexities in general."
                                                        , "The default value is 'automaton'."
                                                        ]
                              , A.defaultValue = Automaton}
                          :+:
                          opt { A.name        = "degree"
                              , A.description = unlines [ "This argument ensures that the complexity induced by the searched matrix interpretation for the weight gap condition is bounded by a"
                                                        , "polynomial of the given degree. Its internal effect is dictated by the value the argument 'cert' is set to."
                                                        , "If it is set to 'algebraic', this restricts the number of non-zero entries in the diagonals of the matrices."
                                                        , "If it is set to 'automaton', this set the paramter 'n' in the criterion 'not IDA(n)'."
                                                        , "Finally, if it is set to 'unrestricted', the effect of setting the 'degree' argument is unspecified."
                                                        ]
                              , A.defaultValue = Nothing}
                          :+:
                          opt { A.name        = "dim"
                              , A.description = unlines [ "This argument specifies the dimension of the vectors and square-matrices appearing"
                                                        , " in the matrix-interpretation for the weight gap condition."]
                              , A.defaultValue = Nat 2 }
                          :+:
                          opt { A.name        = "bound"
                              , A.description = unlines [ "This argument specifies an upper-bound on coefficients appearing in the interpretation."
                                                        , "Such an upper-bound is necessary as we employ bit-blasting to SAT internally"
                                                        , "when searching for compatible matrix interpretations for the weight gap condition."]
                              , A.defaultValue = Nat 3 }
                          :+:
                          opt { A.name        = "bits"
                              , A.description = unlines [ "This argument plays the same role as 'bound',"
                                                        , "but instead of an upper-bound the number of bits is specified."
                                                        , "This argument overrides the argument 'bound'."]
                              , A.defaultValue = Nothing }
                          :+:
                          opt { A.name = "cbits"
                              , A.description = unlines [ "This argument specifies the number of bits used for intermediate results,"
                                                        , "computed for the matrix interpretation of the weight gap condition."]
                              , A.defaultValue = Nothing }
                          :+:
                          opt { A.name = "uargs"
                              , A.description = unlines [ "This argument specifies whether usable arguments are computed (if applicable)"
                                                        , "in order to relax the monotonicity constraints on the interpretation."]
                              , A.defaultValue = True }
--                           :+:
--                           opt { A.name = "uargs"
--                               , A.description = unlines [ "This argument specifies the approximation used for calculating the usable argument"
--                                                         , "positions for the weight gap condition."
--                                                         , "Here 'byFunctions' refers to just looking at defined function symbols, while 'byCap' refers"
--                                                         , "to using a tcap-like function." ]
--                               , A.defaultValue = UArgByCap }

  transform inst prob = do let wgon :+: wgKind :+: wgDeg :+: wgDim :+: wgBound :+: wgBits :+: wgCbits :+: wgUargs = T.transformationArgs inst
                           let (sr, wr) = (Prob.strictComponents prob, Prob.weakComponents prob)
                           let uarg' = if wgUargs then usableArgs (strategy prob) sr wr else fullWithSignature (signature prob)
                           p <- orientMatrix (weightGapConstraints wgon $ strictTrs prob) uarg' (startTerms prob) sr wr (signature prob) (wgKind :+: wgDeg :+: wgDim :+: wgBound :+: wgBits :+: wgCbits :+: wgUargs)
                           return $ case p of
                             (Order (MatrixOrder mi _ _)) -> T.Progress wgpr (enumeration' [prob'])
                               where wgpr   = WeightGapProof { wgInputProblem = prob
                                                             , wgProof        = p
                                                             , wgRemovableDps = Trs.toRules remdps
                                                             , wgRemovableTrs = Trs.toRules remtrs }
                                     remdps = strictRules mi $ strictDPs prob
                                     remtrs = strictRules mi $ strictTrs prob
                                     prob'  = prob { strictDPs = strictDPs prob Trs.\\ remdps
                                                   , strictTrs = strictTrs prob Trs.\\ remtrs
                                                   , weakDPs   = weakDPs prob `Trs.union` remdps
                                                   , weakTrs   = weakTrs prob `Trs.union` remtrs }
                             _                            -> T.NoProgress wgpr
                               where wgpr = WeightGapProof { wgInputProblem = prob
                                                           , wgProof        = p
                                                           , wgRemovableDps = []
                                                           , wgRemovableTrs = [] }

-- applyWeightGap :: P.SolverM m => Bool -> Trs.Trs -> UsablePositions -> Trs.Trs -> Prob.StartTerms -> F.Signature -> NaturalMIKind -> Maybe Nat -> Nat -> N.Size -> Maybe Nat -> Bool
--                -> m (OrientationProof MatrixOrder)
-- applyWeightGap greedy nondup uarg trs st sig mk deg d b bnd cb ua = orientMatrix (weightGapConstraints greedy nondup) uarg' st trs Trs.empty sig (mk :+: deg :+: d :+: (Nat $ N.bound b) :+: Nothing :+: cb :+: ua)
--   where uarg' = if ua then uarg else fullWithSignature sig

weightGapConstraints :: Eq l => WgOn -> Trs.Trs -> UsablePositions -> Prob.StartTerms -> Trs.Trs -> Trs.Trs -> F.Signature -> Domains (S.ArgumentsOf NaturalMI) -> DioFormula l DioVar Int
weightGapConstraints wgon nondup uarg st strict weak sig mp = strictWGConstraints strict absmi && wgonConstraints wgon && weakTrsConstraints absmi weak && otherConstraints
  where absmi      = abstractInterpretation mk d sig :: MatrixInter (DioPoly DioVar Int)
        d          = dim mp
        mk         = kind mp st
        wgonConstraints WgOnTrs = strictTrsConstraints absmi nondup
        wgonConstraints WgOnAny = if Trs.isEmpty strict then top else strictOneConstraints absmi strict
        otherConstraints = slmiSafeRedpairConstraints sig uarg absmi && uargMonotoneConstraints uarg absmi && mkConstraints mk absmi
        mkConstraints UnrestrictedMatrix _ = top
        mkConstraints (TriangularMatrix Nothing) mi = triConstraints mi
        mkConstraints (TriangularMatrix (Just deg)) mi = triConstraints mi && diagOnesConstraints deg mi
        mkConstraints (ConstructorBased cs Nothing) mi = triConstraints mi'
                                                         where mi' = mi{interpretations = filterCs $ interpretations mi}
                                                               filterCs = Map.filterWithKey (\f _ -> f `Set.member` cs)
        mkConstraints (ConstructorBased cs (Just deg)) mi = triConstraints mi' && diagOnesConstraints deg mi'
                                                            where mi' = mi{interpretations = filterCs $ interpretations mi}
                                                                  filterCs = Map.filterWithKey (\f _ -> f `Set.member` cs)
        mkConstraints (EdaMatrix Nothing) mi = edaConstraints mi
        mkConstraints (EdaMatrix (Just deg)) mi = idaConstraints deg mi

strictWGConstraints :: (AbstrOrdSemiring a b, MIEntry a) => Trs -> MatrixInter a -> b
strictWGConstraints trs mi = trsConstraints f mi trs
  where f li ri = bigAnd (zipWith coeffConstraint (Map.elems $ coefficients li) (Map.elems $ coefficients ri))
        coeffConstraint lm rm = row 1 lm .>=. row 1 rm

nondupConstraints :: (AbstrOrdSemiring a b, MIEntry a) => Rule -> MatrixInter a -> b
nondupConstraints r mi = bigAnd $ zipWith coeffConstraint (Map.elems $ coefficients $ interpretTerm mi $ R.lhs r) (Map.elems $ coefficients $ interpretTerm mi $ R.rhs r)
  where coeffConstraint lm rm = row 1 lm .>=. row 1 rm

weightgapProcessor :: T.TransformationProcessor WeightGap P.AnyProcessor
weightgapProcessor = T.transformationProcessor WeightGap

weightgap :: WgOn -> NaturalMIKind -> Maybe Nat -> Nat -> N.Size -> Maybe Nat -> Bool -> T.TheTransformer WeightGap
weightgap wgon wgkind wgdeg wgdim wgsize wgcbits wgua = WeightGap `T.calledWith` (wgon :+: wgkind :+: wgdeg :+: wgdim :+: Nat (N.bound wgsize) :+: Nothing :+: wgcbits :+: wgua)
