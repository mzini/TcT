{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeFamilies #-}

{- | 
Module      :  Tct.Method.DP.DependencyPairs
Copyright   :  (c) Martin Avanzini <martin.avanzini@uibk.ac.at>, 
               Georg Moser <georg.moser@uibk.ac.at>, 
               Andreas Schnabl <andreas.schnabl@uibk.ac.at>
License     :  LGPL (see COPYING)

Maintainer  :  Martin Avanzini <martin.avanzini@uibk.ac.at>
Stability   :  unstable
Portability :  unportable      

This module implements the /weak dependency pair/ transformation.
-}

module Tct.Method.DP.DependencyPairs 
       (
         dependencyPairs
         , dependencyTuples
         -- * Proof Object
         , DPProof (..)
         -- * Processor
         , dependencyPairsProcessor
         , DPs
       )
       where
import Control.Monad (liftM)
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
import Termlib.Trs (Trs, definedSymbols)
import Termlib.Variable(Variables)
import Termlib.Utils
import qualified Tct.Utils.Xml as Xml

import qualified Tct.Processor.Transformations as T
import qualified Tct.Processor as P
import Tct.Processor.Args as A
import Tct.Processor.Args.Instances ()
import Tct.Utils.Enum (enumeration')


markSymbol :: Symbol -> SignatureMonad Symbol
markSymbol f = do fa <- getAttributes f 
                  maybeFresh fa{symIsMarked = True}

dependencyPairsOf :: Bool -> Prob.Problem -> Trs -> [String] -> F.SignatureMonad (Trs, [String])
dependencyPairsOf useTuples prob trs names = do rs <- mapM mk $ zip (Trs.rules trs) names
                                                return $ (Trs.fromRules rs, drop (length rs) names)
    where definedsFromTrs = definedSymbols (Prob.trsComponents prob)
          strat           = Prob.strategy prob
          mk (rule,i) = do lhs' <- mrk $ R.lhs rule
                           rhs' <- mkRhs i $ R.rhs rule
                           return $ R.fromPair (lhs',rhs')
          mkRhs i t   = fromSubterms $ gatherSubterms t
              where -- fromSubterms [t1] = mrk t1
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
    pprint NotRCProblem = paragraph "The input problem is not a RC-problem. We cannot compute dependency pairs."
    pprint ContainsDPs  = paragraph "The input problem contains already dependency pairs. "
    pprint TuplesNonInnermost  = paragraph "Dependency tuples only applicable to innermost problems."
    pprint p            = paragraph ("We add the following " 
                                     ++ (if tuplesUsed p then "dependency tuples" else "weak dependency pairs") ++ ":")
                          $+$ text ""
                          $+$ ppTrs "Strict DPs" (strictDPs p)
                          $+$ ppTrs  "Weak DPs" (weakDPs p)
                          $+$ text ""
                          $+$ paragraph "and mark the set of starting terms."
        where sig = newSignature p
              vars = newVariables p
              ppTrs = pprintNamedTrs sig vars

instance T.TransformationProof DPs where
    answer = T.answerFromSubProof
    pprintTProof _ _ p _ = pprint p
    tproofToXml _ _ NotRCProblem = ("dp", [Xml.elt "NotRcProblem" [] []])
    tproofToXml _ _ ContainsDPs = ("dp", [Xml.elt "containsDPs" [] []])
    tproofToXml _ _ TuplesNonInnermost = ("dp", [Xml.elt "tuplesNonInnermost" [] []])
    tproofToXml _ _ p = 
      ( "dp"
      , [ Xml.elt (if tuplesUsed p then "tuples" else "pairs") [] []
        , Xml.elt "strictDPs" [] [Xml.rules (strictDPs p) sig vs]
        , Xml.elt "weakDPs" [] [Xml.rules (weakDPs p) sig vs]])
      where sig = newSignature p
            vs = newVariables p
      
instance T.Transformer DPs where
    name DPs = "dp"
    instanceName inst | tups = "Dependency Tuples"
                      | otherwise = "Weak Dependency Pairs"
       where tups = T.transformationArgs inst
    description DPs = ["Applies the (weak) depencency pair transformation."]

    type ArgumentsOf DPs = Arg Bool
    type ProofOf DPs = DPProof
    arguments DPs = opt { A.name = "usetuples"
                        , A.description = unlines [ "This argument specifies whether dependency tuples instead of pairs should be used."]
                        , A.defaultValue = False }

    transform inst prob = return $  
        case (Prob.startTerms prob, Trs.isEmpty $ Prob.dpComponents prob, useTuples && (Prob.strategy prob /= Innermost)) of 
          (TermAlgebra _   , _    ,    _) -> T.NoProgress NotRCProblem
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

dependencyPairsProcessor :: T.Transformation DPs P.AnyProcessor
dependencyPairsProcessor = T.Transformation DPs

-- | Implements dependency pair transformation. Only applicable on runtime-complexity problems.
dependencyPairs :: T.TheTransformer DPs
dependencyPairs = T.Transformation DPs `T.withArgs` False

-- | Implements dependency tuples transformation. Only applicable on innermost runtime-complexity problems.
dependencyTuples :: T.TheTransformer DPs
dependencyTuples = T.Transformation DPs `T.withArgs` True


                                          -- 
