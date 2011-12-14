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
import Control.Monad (liftM, foldM)
-- import Control.Monad.Trans (liftIO)
import qualified Data.Set as Set
import Text.PrettyPrint.HughesPJ hiding (empty)

import qualified Termlib.FunctionSymbol as F
import qualified Termlib.Problem as Prob
import Termlib.Problem (Strategy (..), StartTerms (..))
import qualified Termlib.Term as Term
import qualified Termlib.Rule as R
import Termlib.FunctionSymbol hiding (lookup)
import qualified Termlib.Signature as Sig
import qualified Termlib.Trs as Trs
import Termlib.Trs.PrettyPrint (pprintNamedTrs)
import Termlib.Trs (Trs(..), definedSymbols)
import Termlib.Variable(Variables)
import Termlib.Utils

import qualified Tct.Processor.Transformations as T
import qualified Tct.Processor as P
import Tct.Processor.Args as A
import Tct.Processor.Args.Instances ()
import Tct.Processor.PPrint (enumeration')


markSymbol :: Symbol -> SignatureMonad Symbol
markSymbol f = do fa <- getAttributes f 
                  maybeFresh fa{symIsMarked = True}

dependencyPairsOf :: Bool -> Prob.Problem -> Trs -> [String] -> F.SignatureMonad (Trs, [String])
dependencyPairsOf useTuples prob trs names = do rs <- mapM mk $ zip (rules trs) names
                                                return $ (Trs rs, drop (length rs) names)
    where definedsFromTrs = definedSymbols (Prob.trsComponents prob)
          strat           = Prob.strategy prob
          mk (rule,i) = do lhs' <- mrk $ R.lhs rule
                           rhs' <- mkRhs i $ R.rhs rule
                           return $ R.fromPair (lhs',rhs')
          mkRhs i t   = fromSubterms $ gatherSubterms t
              where fromSubterms [t1] = mrk t1
                    fromSubterms ts = do c <- fresh (defaultAttribs i (length ts)) {symIsCompound = True}
                                         ts' <- mapM mrk ts
                                         return $ Term.Fun c ts'
                    gatherSubterms | useTuples = gatherSubtermsWDT
                                   | otherwise = gatherSubtermsWDP
                    gatherSubtermsWDP v@(Term.Var _) | strat == Innermost = []
                                                     | otherwise         = [v]
                    gatherSubtermsWDP s@(Term.Fun f ss) | f `Set.member` definedsFromTrs = [s]
                                                        | otherwise                      = concatMap gatherSubterms ss
                    gatherSubtermsWDT s@(Term.Fun f ss) | f `Set.member` definedsFromTrs = s : subs
                                                        | otherwise                      = subs
                        where subs = concatMap gatherSubterms ss                                                                                           
                    gatherSubtermsWDT _                                                  = []                                                                                           

                    
                                                                                           
          mrk v@(Term.Var _) = return $ v
          mrk (Term.Fun f ts) = do f' <- markSymbol f
                                   return $ Term.Fun f' ts

data DPs = DPs

data DPProof = DPProof { strictDPs    :: Trs
                       , weakDPs      :: Trs
                       , tuplesUsed   :: Bool
                       , newSignature :: Signature
                       , newVariables :: Variables }
             | NotRCProblem
             | ContainsDPs
             | TuplesNonInnermost

instance PrettyPrintable DPProof where 
    pprint NotRCProblem = text "The input problem is not a RC-problem. We cannot compute dependency pairs."
    pprint ContainsDPs  = text "The input problem contains already dependency pairs. "
    pprint TuplesNonInnermost  = text "Dependency tuples only applicable to innermost problems."
    pprint p            = text "We have computed the following dependency pairs"
                          $+$ text ""
                          $+$ nest 2 (ppTrs "Strict DPs" (strictDPs p)
                                      $+$ ppTrs  "Weak DPs" (weakDPs p))
        where sig = newSignature p
              vars = newVariables p
              ppTrs = pprintNamedTrs sig vars

instance T.TransformationProof DPs where
    answer = T.answerFromSubProof
    pprintTProof _ _ = pprint

instance T.Transformer DPs where
    name DPs = "dp"
    description DPs = ["Applies the Depencency Pair Transformation"]

    type T.ArgumentsOf DPs = Arg Bool
    type T.ProofOf DPs = DPProof
    arguments DPs = opt { A.name = "usetuples"
                        , A.description = unlines [ "This argument specifies whether dependency tuples instead of pairs should be used."]
                        , A.defaultValue = False }

    transform inst prob = return $  
        case (Prob.startTerms prob, Trs.isEmpty $ Prob.dpComponents prob, useTuples && (Prob.strategy prob /= Innermost)) of 
          (TermAlgebra     , _    ,    _) -> T.NoProgress NotRCProblem
          (_               , False,    _) -> T.NoProgress ContainsDPs
          (_               , _    , True) -> T.NoProgress TuplesNonInnermost
          (BasicTerms ds cs, _    , _   ) -> T.Progress proof  (enumeration' [prob'])
            where sig       = Prob.signature prob
                  strict    = Prob.strictTrs prob
                  weak      = Prob.weakTrs prob
                  ((sDps, wDps, ds'), sig') = flip Sig.runSignature sig $ 
                                              do (s,names) <- dependencyPairsOf useTuples prob strict ["c_" ++ show i | i <- [ (1:: Int)..]]
                                                 (w,_) <- dependencyPairsOf useTuples prob weak names
                                                 d <- Set.fromList `liftM` (mapM markSymbol $ Set.elems ds)
                                                 return (s, w, d)
                  proof     = DPProof { strictDPs = sDps
                                      , weakDPs   = wDps
                                      , newSignature = sig'
                                      , newVariables = Prob.variables prob 
                                      , tuplesUsed   = useTuples}
                  prob'     = prob { Prob.startTerms = BasicTerms ds' cs
                                   , Prob.strictDPs  = sDps
                                   , Prob.weakDPs    = wDps
                                   , Prob.strictTrs = if useTuples then Trs.empty else Prob.strictTrs prob
                                   , Prob.weakTrs   = if useTuples 
                                                       then Prob.trsComponents prob
                                                       else Prob.weakTrs prob
                                   , Prob.signature  = sig' }
        where useTuples = T.transformationArgs inst


withFreshCompounds :: Prob.Problem -> Prob.Problem
withFreshCompounds prob = fst . flip Sig.runSignature (Prob.signature prob)  $ 
                          do (nxt,sdps') <- foldM frsh (1::Int, []) sdps 
                             (_  ,wdps') <- foldM frsh (nxt  , []) wdps 
                             sig' <- Sig.getSignature
                             return $ prob { Prob.signature = sig'
                                           , Prob.strictDPs = Trs.fromRules sdps'
                                           , Prob.weakDPs = Trs.fromRules wdps'}
   where sdps = Trs.rules $ Prob.strictDPs prob
         wdps = Trs.rules $ Prob.weakDPs prob
         frsh (i, dps) rl = 
           case R.rhs rl of 
             Term.Var _    -> return (i, rl:dps)
             Term.Fun f rs -> 
               do attribs <- getAttributes f
                  case (symIsCompound attribs, rs) of 
                    (False, _)   -> return (i, rl:dps)
                    (True , [r]) -> return (i, rl{ R.rhs = r }:dps)
                    _            -> do c <- frshCompound i (length rs)
                                       return (i+1, rl{ R.rhs = Term.Fun c rs}:dps) 
         frshCompound i ar = fresh (defaultAttribs ("c_" ++ show i) ar) {symIsCompound = True}

dependencyPairsProcessor :: T.TransformationProcessor DPs P.AnyProcessor
dependencyPairsProcessor = T.transformationProcessor DPs

dependencyPairs :: T.TheTransformer DPs
dependencyPairs = DPs `T.calledWith` False

dependencyTuples :: T.TheTransformer DPs
dependencyTuples = DPs `T.calledWith` True


                                          -- 
