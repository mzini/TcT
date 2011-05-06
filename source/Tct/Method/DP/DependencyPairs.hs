{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeFamilies #-}
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
module Tct.Method.DP.DependencyPairs where
import qualified Control.Monad.State.Lazy as State
import Data.List (partition, intersperse, delete, sortBy)
import qualified Data.List as List
import Control.Monad (liftM)
-- import Control.Monad.Trans (liftIO)
import qualified Data.Set as Set
import Data.Typeable 
import Data.Maybe (fromJust, isJust, fromMaybe, mapMaybe)
import qualified Text.PrettyPrint.HughesPJ as PP 
import Text.PrettyPrint.HughesPJ hiding (empty)

import qualified Qlogic.NatSat as N

import qualified Termlib.FunctionSymbol as F
import qualified Termlib.Problem as Prob
import Termlib.Problem (Problem, StartTerms (..), Strategy(..))
import qualified Termlib.Term as Term
import Termlib.Term (Term)
import qualified Termlib.Rule as R
import Termlib.FunctionSymbol hiding (lookup)
import qualified Termlib.Signature as Sig
import Termlib.Rule (Rule)
import qualified Termlib.Trs as Trs
import Termlib.Trs.PrettyPrint (pprintTrs)
import Termlib.Trs (Trs(..), definedSymbols)
import Termlib.Variable(Variables)
import Termlib.Utils

import Tct.Certificate
import qualified Tct.Processor.Transformations as T
import qualified Tct.Processor as P
import Tct.Processor (succeeded, answer, certificate, answerFromCertificate, Answer(..), Answerable(..))
import Tct.Method.Matrix.NaturalMI (MatrixOrder, NaturalMIKind(..))
import Tct.Processor.Args as A
import Tct.Processor.Args.Instances
import Tct.Processor.PPrint (enumeration')
import Tct.Encoding.UsablePositions
import Tct.Processor.Orderings
import Tct.Method.Weightgap (applyWeightGap)


markSymbol :: Symbol -> SignatureMonad Symbol
markSymbol f = do fa <- getAttributes f 
                  maybeFresh fa{symIsMarked = True}

dependencyPairsOf :: Bool -> Strategy -> Trs -> F.SignatureMonad Trs
dependencyPairsOf useTuples strat trs = Trs `liftM` (mapM mk $ zip (rules trs) ([0..] :: [Int]))
    where definedsFromTrs = definedSymbols trs 
          mk (rule,i) = do lhs' <- mrk $ R.lhs rule
                           rhs' <- mkRhs i $ R.rhs rule
                           return $ R.fromPair (lhs',rhs')
          mkRhs i t   = fromSubterms $ gatherSubterms t
              where fromSubterms ts = do c <- fresh (defaultAttribs ("c_" ++ show i) (length ts)) {symIsCompound = True}
                                         ts' <- mapM mrk ts
                                         return $ Term.Fun c ts'
                    gatherSubterms v@(Term.Var _) | strat == Innermost = []
                                                  | otherwise         = [v]
                    gatherSubterms s@(Term.Fun f ss) | f `Set.member` definedsFromTrs = [s]
                                                     | otherwise                      = concatMap gatherSubterms ss
          mrk v@(Term.Var _) = return $ v
          mrk (Term.Fun f ts) = do f' <- markSymbol f
                                   return $ Term.Fun f' ts

data DPs = DPs

data DPProof = DPProof { strictDPs    :: Trs
                       , weakDPs      :: Trs
                       , newSignature :: Signature
                       , newVariables :: Variables }
             | NotRCProblem
             | ContainsDPs

instance PrettyPrintable DPProof where 
    pprint NotRCProblem = text "The input problem is not a RC-problem. We cannot compute dependency pairs."
    pprint ContainsDPs  = text "The input problem contains already dependency pairs. We abort."
    pprint p            = text "We have computed the following dependency pairs"
                          $+$ block "Strict Dependency Pairs" (pprint (strictDPs p, sig, vars))
                          $+$ block "Weak Dependency Pairs" (pprint (weakDPs p, sig, vars))
        where sig = newSignature p
              vars = newVariables p

instance P.Processor sub => P.Answerable (T.TProof DPs sub) where
    answer = T.answerTProof answer'
        where answer' _ [(_,p)] = P.answer p
              answer' _ _       = error "dependency pairs processor received wrong number of subproofs"

instance P.Processor sub => PrettyPrintable (T.TProof DPs sub) where
    pprint = T.prettyPrintTProof

instance T.Verifiable DPProof

instance T.Transformer DPs where
    name DPs = "Dependency Pair Transformation"
    description DPs = ["Applies the Depencency Pair Transformation"]

    type T.ArgumentsOf DPs = Arg Bool
    type T.ProofOf DPs = DPProof
    arguments DPs = opt { A.name = "usetuples"
                        , A.description = unlines [ "This argument specifies whether dependency tuples instead of pairs should be used."]
                        , A.defaultValue = False }

    transform inst prob = return $  
        case (Prob.startTerms prob, Trs.isEmpty $ Prob.dpComponents prob) of 
          (TermAlgebra     , _    ) -> T.Failure NotRCProblem
          (_               , False) -> T.Failure ContainsDPs
          (BasicTerms ds cs, _    ) -> T.Success proof  (enumeration' [prob'])
              where useTuples = T.transformationArgs inst
                    strat     = Prob.strategy prob
                    sig       = Prob.signature prob
                    strict    = Prob.strictTrs prob
                    weak      = Prob.weakTrs prob
                    ((sDps, wDps, ds'), sig') = flip Sig.runSignature sig $ 
                                                do s <- dependencyPairsOf useTuples strat strict
                                                   w <- dependencyPairsOf useTuples strat weak
                                                   d <- Set.fromList `liftM` (mapM markSymbol $ Set.elems ds)
                                                   return (s, w, d)
                    proof     = DPProof { strictDPs = sDps
                                        , weakDPs   = wDps
                                        , newSignature = sig'
                                        , newVariables = Prob.variables prob }
                    prob'     = prob { Prob.startTerms = BasicTerms ds' cs
                                     , Prob.strictDPs  = sDps
                                     , Prob.weakDPs    = wDps }


dependencyPairsProcessor :: T.TransformationProcessor DPs P.AnyProcessor
dependencyPairsProcessor = T.transformationProcessor DPs

dependencyPairs :: (P.Processor sub) => Bool -> P.InstanceOf sub -> P.InstanceOf (T.TransformationProcessor DPs sub)
dependencyPairs useTuples = T.transformationProcessor DPs `T.calledWith` useTuples


                                          -- 
