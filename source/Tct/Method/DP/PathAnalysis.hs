{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeSynonymInstances #-}

--------------------------------------------------------------------------------
-- | 
-- Module      :  Tct.Method.DP.PathAnalysis
-- Copyright   :  (c) Martin Avanzini <martin.avanzini@uibk.ac.at>, 
--                Georg Moser <georg.moser@uibk.ac.at>, 
--                Andreas Schnabl <andreas.schnabl@uibk.ac.at>,
-- License     :  LGPL (see COPYING)
--
-- Maintainer  :  Martin Avanzini <martin.avanzini@uibk.ac.at>
-- Stability   :  unstable
-- Portability :  unportable      
-- 
-- This module provides the path analysis with respect to dependency
-- graphs.
--------------------------------------------------------------------------------   

module Tct.Method.DP.PathAnalysis 
       (
         pathAnalysis
         -- * Proof Object
       , PathProof
         -- * Processor
       , pathAnalysisProcessor
       , PathAnalysis
       )
where

import qualified Data.List as List
import Control.Monad (liftM)
import Control.Applicative ((<|>))
-- import Control.Monad.Trans (liftIO)
import Data.Maybe (fromMaybe)
import Data.Either (partitionEithers)
import qualified Text.PrettyPrint.HughesPJ as PP 
import Text.PrettyPrint.HughesPJ hiding (empty)

import qualified Termlib.FunctionSymbol as F
import qualified Termlib.Problem as Prob
import qualified Termlib.Trs as Trs
import qualified Termlib.Variable as V
import Termlib.Utils

import Tct.Certificate
import Tct.Method.DP.DependencyGraph
import qualified Tct.Processor.Transformations as T
import qualified Tct.Processor as P
import Tct.Processor.Args as A
import Tct.Utils.PPrint
import Tct.Utils.Enum
import Tct.Processor.Args.Instances ()
import Tct.Method.DP.Utils

----------------------------------------------------------------------
-- Proof objects

data Path = Path { thePath :: [NodeId] } deriving (Eq, Show)

data PathProof = PathProof { computedPaths   :: [Path]
                           , computedCongrDG :: CDG
                           , computedDG      :: DG
                           , subsumedBy      :: [(Path,[Path])]
                           , variables       :: V.Variables
                           , signature       :: F.Signature
                           , isLinearProof   :: Bool}
                 | Error DPError

data PathAnalysis = PathAnalysis

instance T.Transformer PathAnalysis where
    name PathAnalysis        = "pathanalysis"
    description PathAnalysis = ["This processor implements path-analysis as described in the dependency pair paper."]
    type T.ArgumentsOf PathAnalysis = Arg Bool
    type T.ProofOf PathAnalysis = PathProof
    arguments PathAnalysis = opt { A.name = "linear"
                                 , A.description = unlines [ "If this flag is set, linear path analysis is employed."]
                                 , A.defaultValue = False }
    transform inst prob 
           | not $ Prob.isDPProblem prob = return $ T.NoProgress $ Error NonDPProblemGiven
           | otherwise                 = return $ res
        where lin = T.transformationArgs inst
              res | progressed = T.Progress p (enumeration [(thePath pth, prob') | (pth,prob') <- pathsToProbs ])
                  | otherwise  = T.NoProgress p
              edg  = estimatedDependencyGraph Edg prob
              cedg = toCongruenceGraph edg
              rts  = roots cedg
              lfs  = leafs cedg
              p = PathProof { computedPaths   = paths
                            , computedCongrDG = cedg
                            , computedDG      = edg
                            , subsumedBy      = subsume
                            , variables       = Prob.variables prob
                            , signature       = Prob.signature prob
                            , isLinearProof   = lin}
              (subsume, pathsToProbs) = partitionEithers $ concatMap (walkFrom []) rts
              paths = [pth | (pth, _) <- subsume] ++ [pth | (pth,_) <- pathsToProbs]

              walkFrom | lin       = walkFromL
                       | otherwise = walkFromQ Trs.empty
              walkFromL prefix n = new ++ concatMap (walkFromL path) sucs
                  where path = prefix ++ [n]
                        sucs = List.nub $ successors cedg n
                        new | null sucs = [Right ( Path path
                                          , prob { Prob.strictDPs = stricts, Prob.weakDPs = weaks} )]
                            | otherwise = []
                        rs      = allRulesFromNodes cedg path
                        stricts = Trs.fromRules [ r | (StrictDP, r) <- rs]
                        weaks   = Trs.fromRules [ r | (WeakDP, r) <- rs]
                          
              walkFromQ weaks prefix n = new ++ concatMap (walkFromQ weaks' path) sucs
                  where path = prefix ++ [n]
                        sucs = List.nub $ successors cedg n
                        rs = allRulesFromNodes cedg [n]
                        strict_n = Trs.fromRules [ r | (StrictDP, r) <- rs]
                        weak_n = Trs.fromRules [ r | (WeakDP, r) <- rs]
                        weaks' = strict_n `Trs.union` weak_n `Trs.union` weaks
                        new | subsumed  = [Left  ( Path path, [Path $ path ++ [n'] | n' <- sucs ] )]
                            | otherwise = [Right ( Path path
                                                 , prob { Prob.strictDPs = strict_n, Prob.weakDPs = weaks} )]
                            where subsumed = not (null sucs) && Trs.isEmpty strict_n

              progressed | lin = length (rts ++ lfs) > 2
                         | otherwise = 
                            case paths of 
                               [pth] -> length spath < length sprob
                                   where spath = [ r | (StrictDP, r) <- allRulesFromNodes cedg (thePath pth) ]
                                         sprob = Trs.toRules $ Prob.strictDPs prob
                               _     -> True

printPathName :: CDG -> F.Signature -> V.Variables -> Path -> Doc
printPathName cwdg sig vars (Path ns) = hcat $ punctuate (text "->") [printNodeId n | n <- ns] 
  where printNodeId = pprintCWDGNode cwdg sig vars 


instance T.TransformationProof PathAnalysis where
    answer proof = case T.transformationResult proof of 
                     T.NoProgress _ -> T.answerFromSubProof proof
                     T.Progress _ subprobs -> 
                         case mproofs of 
                           Just proofs -> if all P.succeeded proofs
                                          then P.CertAnswer $ certified (unknown, mkUb proofs)
                                          else P.MaybeAnswer
                           Nothing  -> P.NoAnswer
                         where mproofs = sequence [ T.findProof e proof | (SN e,_) <- subprobs]
                               mkUb proofs = maximum $ (Poly $ Just 1) : [upperBound $ P.certificate p | p <- proofs]
                           
    pprintProof proof mde = 
        case T.transformationProof proof of 
          Error   e   -> pprint e
          tproof -> text "We use following congruence DG for" <+> text nm
                   $+$ text ""
                   $+$ pprintCWDG cwdg sig vars ppLabel
                   $+$ text ""
                   $+$ ppDetails
              where cwdg = computedCongrDG tproof
                    sig = signature tproof
                    vars = variables tproof
  
                    nm | isLinearProof tproof = "linear path analysis"
                       | otherwise            = "path analysis"
                    ppLabel pth _ = PP.brackets $ centering 20 $ ppMaybeAnswerOf (Path pth)
                        where centering n d =  text $ take pre ss ++ s ++ take post ss
                                  where s = show d
                                        l = length s
                                        ss = repeat ' '
                                        pre = floor $ (fromIntegral (n - l) / 2.0 :: Double)
                                        post = n - l - pre

                    ppMaybeAnswerOf pth = fromMaybe (text "?") (ppSpAns <|> ppSubsumed)
                        where ppSpAns    = pprint `liftM` P.answer `liftM` findSubProof pth
                              ppSubsumed = const (text "subsumed") `liftM` List.lookup pth (subsumedBy tproof)

                    findSubProof pth = T.findProof (thePath pth) proof

                    ppPathName path = printPathName cwdg sig vars path

                    ppDetails = vcat $ List.intersperse (text "") 
                                         [ (text "*" <+> (underline (text "Path" <+> ppPathName path <> text ":" <+> ppMaybeAnswerOf path)
                                                          $+$ text ""
                                                          $+$ ppDetail path))
                                           | path <- List.sortBy comparePath $ computedPaths tproof]
                        where comparePath p1 p2 = mkpath p1 `compare` mkpath p2
                              mkpath p = [congruence cwdg n | n <- thePath p]
                              ppDetail path = fromMaybe errMsg (ppsubsumed <|> ppsubproof)
                                  where errMsg = text "CANNOT find proof of path" <+> ppPathName path <> text "." 
                                                 <+> text "Propably computation has been aborted since some other path cannot be solved."
                                        ppsubsumed = do paths <- List.lookup path (subsumedBy tproof)
                                                        return $ (text "This path is subsumed by the proof of paths" 
                                                                  <+> sep (punctuate (text ",") [ppPathName pth | pth <- paths])
                                                                  <> text ".")
                                        ppsubproof = do subproof <- findSubProof path
                                                        return $ P.pprintProof subproof mde

    pprintTProof _ _ (Error e) = pprint e
    pprintTProof _ _ tproof    = block' "Transformation Details" [ppTrans]
        where ppTrans = paragraph "Following congruence DG was used:"
                        $+$ text ""
                        $+$ pprintCWDG cwdg (signature tproof) (variables tproof) (\ _ _ -> text "")
              cwdg = computedCongrDG tproof





pathAnalysisProcessor :: T.Transformation PathAnalysis P.AnyProcessor
pathAnalysisProcessor = T.Transformation PathAnalysis

-- | Implements path analysis. If the given argument is 'True', then
-- linear path analysis is employed.
pathAnalysis :: Bool -> T.TheTransformer PathAnalysis
pathAnalysis lin = T.Transformation PathAnalysis `T.withArgs` lin
