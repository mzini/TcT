
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeSynonymInstances #-}

module Tct.Method.DP.PathAnalysis where

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
import Termlib.Trs (Trs(..))
import qualified Termlib.Variable as V
import Termlib.Utils

import Tct.Certificate
import Tct.Method.DP.DependencyGraph
import qualified Tct.Processor.Transformations as T
import qualified Tct.Processor as P
import Tct.Processor.Args as A
import Tct.Processor.PPrint
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
                           , signature       :: F.Signature}
                 | Error DPError

data PathAnalysis = PathAnalysis

instance T.Transformer PathAnalysis where
    name PathAnalysis        = "pathanalysis"
    description PathAnalysis = ["Pathanalysis"]
    type T.ArgumentsOf PathAnalysis = Unit
    type T.ProofOf PathAnalysis = PathProof
    arguments PathAnalysis = Unit
    transform _ prob | not $ Prob.isDPProblem prob = return $ T.NoProgress $ Error NonDPProblemGiven
                     | otherwise                 = return $ res
        where res | progressed = T.Progress p (enumeration [(thePath pth, prob') | (pth,prob') <- pathsToProbs ])
                  | otherwise  = T.NoProgress p
              edg  = estimatedDependencyGraph Edg prob
              cedg = toCongruenceGraph edg
              p = PathProof { computedPaths   = paths
                            , computedCongrDG = cedg
                            , computedDG      = edg
                            , subsumedBy      = subsume
                            , variables       = Prob.variables prob
                            , signature       = Prob.signature prob}
              (subsume, pathsToProbs) = partitionEithers $ concatMap (walkFrom [] Trs.empty) (roots cedg)
              paths = [pth | (pth, _) <- subsume] ++ [pth | (pth,_) <- pathsToProbs]

              walkFrom prefix weaks n = new ++ concatMap (walkFrom path weaks') (successors cedg n)
                  where path = prefix ++ [n]
                        sucs = successors cedg n
                        rs = allRulesFromNodes cedg [n]
                        strict_n = Trs.fromRules [ r | (StrictDP, r) <- rs]
                        weak_n = Trs.fromRules [ r | (WeakDP, r) <- rs]
                        weaks' = strict_n `Trs.union` weak_n `Trs.union` weaks
                        new | subsumed  = [Left  ( Path path, [Path $ path ++ [n'] | n' <- sucs ] )]
                            | otherwise = [Right ( Path path
                                                 , prob { Prob.strictDPs = strict_n, Prob.weakDPs = weaks} )]
                            where subsumed = not (null sucs) && Trs.isEmpty strict_n

              progressed = case paths of 
                             [pth] -> length spath < length sprob
                                 where spath = [ r | (StrictDP, r) <- allRulesFromNodes cedg (thePath pth) ]
                                       Trs sprob = Prob.strictDPs prob
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
                                          then P.answerFromCertificate $ certified (unknown, mkUb proofs)
                                          else P.MaybeAnswer
                           Nothing  -> P.NoAnswer
                         where mproofs = sequence [ T.findProof e proof | (SN e,_) <- subprobs]
                               mkUb proofs = maximum $ (Poly $ Just 1) : [upperBound $ P.certificate p | p <- proofs]
                           
    pprint proof = case T.transformationProof proof of 
                     Error   e   -> pprint e
                     tproof -> text "We use following congruence DG for path analysis"
                               $+$ text ""
                               $+$ pprintCWDG cwdg sig vars ppLabel
                                $+$ text ""
                               $+$ ppDetails
                         where cwdg = computedCongrDG tproof
                               sig = signature tproof
                               vars = variables tproof
  
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

                               ppDetails = vcat $ List.intersperse (text "") [ (text "*" <+> (underline (text "Path" <+> ppPathName path <> text ":" <+> ppMaybeAnswerOf path)
                                                                                              $+$ text ""
                                                                                              $+$ ppDetail path))
                                                                               | path <- List.sortBy comparePath $ computedPaths tproof]
                                   where comparePath p1 p2 = mkpath p1 `compare` mkpath p2
                                             where mkpath p = [congruence cwdg n | n <- thePath p]
                                         ppDetail path = fromMaybe errMsg (ppsubsumed <|> ppsubproof)
                                             where errMsg = text "CANNOT find proof of path" <+> ppPathName path <> text "." 
                                                            <+> text "Propably computation has been aborted since some other path cannot be solved."
                                                   ppsubsumed = do paths <- List.lookup path (subsumedBy tproof)
                                                                   return $ (text "This path is subsumed by the proof of paths" 
                                                                             <+> sep (punctuate (text ",") [ppPathName pth | pth <- paths])
                                                                             <> text ".")
                                                   ppsubproof = do subproof <- findSubProof path
                                                                   return $ pprint subproof

    pprintProof _ _ (Error e) = pprint e
    pprintProof _ _ tproof    = block' "Transformation Details" [ppTrans]
        where ppTrans = paragraph "Following congruence DG was used:"
                        $+$ text ""
                        $+$ pprintCWDG cwdg (signature tproof) (variables tproof) (\ _ _ -> text "")
              cwdg = computedCongrDG tproof





pathAnalysisProcessor :: T.TransformationProcessor PathAnalysis P.AnyProcessor
pathAnalysisProcessor = T.transformationProcessor PathAnalysis

pathAnalysis :: T.TheTransformer PathAnalysis
pathAnalysis = PathAnalysis `T.calledWith` ()
