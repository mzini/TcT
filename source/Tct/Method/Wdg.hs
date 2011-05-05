
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeSynonymInstances #-}

module Tct.Method.Wdg where

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
import Termlib.Problem
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
import Tct.Method.DP.DependencyGraph
import Tct.Method.DP.UsableRules
import Tct.Method.DP.DependencyPairs
import qualified Tct.Processor.Transformations as T
import qualified Tct.Processor as P
import Tct.Processor (succeeded, answer, certificate, answerFromCertificate, Answer(..), Answerable(..))
import Tct.Method.Matrix.NaturalMI (MatrixOrder, NaturalMIKind(..))
import Tct.Processor.Args as A
import Tct.Processor.PPrint
import Tct.Processor.Args.Instances
import Tct.Encoding.UsablePositions
import Tct.Processor.Orderings
import Tct.Method.Weightgap (applyWeightGap)


----------------------------------------------------------------------
-- Proof objects

data Path = Path { thePath     :: Graph.Path
                 , pathTrss    :: ([Trs],Trs)
                 , pathUsables :: Trs } deriving Show

data PathProof = PPSubsumedBy Path
               | PPWeightGap (OrientationProof MatrixOrder) deriving Show

data WdgProof = WdgProof { computedPaths     :: [(Path, PathProof)]
                         , computedGraph     :: Graph
                         , computedGraphSCC  :: SCCGraph
                         , dependencyPairs   :: Trs
                         , usableRules       :: Trs
                         , newSignature      :: Signature
                         , newVariables      :: Variables
                         , containsNoEdgesEmptyUrs :: Bool
                         , tuplesUsed        :: Bool}
              | NA { reason :: String }



----------------------------------------------------------------------
-- Processor


data Wdg = Wdg

wdgProcessor :: T.TransformationProcessor Wdg P.AnyProcessor
wdgProcessor = T.transformationProcessor Wdg

wdg :: (P.Processor sub) => Approximation -> Bool -> NaturalMIKind -> Maybe Nat -> Nat -> N.Size -> Maybe Nat -> Bool -> Bool -> P.InstanceOf sub -> P.InstanceOf (T.TransformationProcessor Wdg sub)
wdg approx weightgap wgkind wgdeg wgdim wgsize wgcbits ua tuples = T.transformationProcessor Wdg `T.calledWith` (approx :+: weightgap :+: wgkind :+: wgdeg :+: wgdim :+: Nat (N.bound wgsize) :+: Nothing :+: wgcbits :+: ua :+: tuples)

instance T.Transformer Wdg where
    name Wdg = "wdg"
    description Wdg = ["This processor implements path analysis based on (weak) dependency graphs."]

    type T.ArgumentsOf Wdg = (Arg (EnumOf Approximation)) :+: (Arg Bool) :+: (Arg (EnumOf NaturalMIKind)) :+: (Arg (Maybe Nat)) :+: (Arg Nat) :+: (Arg Nat) :+: (Arg (Maybe Nat)) :+: (Arg (Maybe Nat)) :+: (Arg Bool) :+: (Arg Bool)
    type T.ProofOf Wdg = WdgProof 
    instanceName _ = "Dependency Graph Analysis"
    arguments _ = opt { A.name = "approximation"
                      , A.defaultValue = Edg
                      , A.description = "specifies the employed dependency graph approximation"}
                  :+:
                  opt { A.name = "weightgap"
                      , A.defaultValue = True
                      , A.description = "specifies whether the weightgap principle is used per path"}
                  :+:
                  opt { A.name        = "cert"
                      , A.description = unlines [ "This argument specifies restrictions on the matrix-interpretation which induce polynomial growth of"
                                                , "the interpretation of the considered starting terms relative to their size for the weight gap condition."
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
                  opt { A.name = "degree"
                      , A.description = unlines [ "This argument ensures that the complexity induced by the matrix interpretation for the weight gap condition is bounded by a"
                                                , "polynomial of the given degree. Its internal effect is dictated by the value the argument 'cert' is set to."
                                                , "If it is set to 'algebraic', this restricts the number of non-zero entries in the diagonals of the matrices."
                                                , "If it is set to 'automaton', this set the paramter 'n' in the criterion 'not IDA(n)'."
                                                , "Finally, if it is set to 'unrestricted', the effect of setting the 'degree' argument is unspecified."
                                                ]
                      , A.defaultValue = Nothing}
                  :+:
                  opt { A.name = "dim"
                      , A.description = unlines [ "This argument specifies the dimension of the vectors and square-matrices appearing"
                                                , "in the matrix-interpretation for the weight gap condition."]
                      , A.defaultValue = Nat 2 }
                  :+:
                  opt { A.name = "bound"
                      , A.description = unlines [ "This argument specifies an upper-bound on coefficients appearing in the matrix"
                                                , "interpretation for the weight gap condition."]
                      , A.defaultValue = Nat 3 }
                  :+:
                  opt { A.name = "bits"
                      , A.description = unlines [ "This argument plays the same role as 'bound',"
                                                , "but instead of an upper-bound the number of bits is specified."
                                                , "This argument overrides the argument 'bound'." ]
                      , A.defaultValue = Nothing }
                  :+:
                  opt { A.name = "cbits"
                      , A.description = unlines [ "This argument specifies the number of bits used for intermediate results"
                                                , "computed for the matrix interpretation of the weight gap condition." ]
                      , A.defaultValue = Nothing }
                  :+:
                  opt { A.name = "uargs"
                      , A.description = unlines [ "This argument specifies whether usable arguments are computed (if applicable)"
                                                , "in order to relax the monotonicity constraints on the interpretation."]
                      , A.defaultValue = True }
                  :+:
                  opt { A.name = "tuples"
                      , A.description = unlines [ "Specifies whether Dependency-Tuples should be used for the innermost case."]
                      , A.defaultValue = False }

    transform inst prob =
        case (startTerms prob, relation prob) of 
          (TermAlgebra, _) -> return $ T.Failure $ NA {reason = "derivational complexity"}
          (_, DP _ _) -> return $ T.Failure $ NA {reason = "DP problems"}
          (_, Relative _ _) -> return $ T.Failure $ NA {reason = "relative problems"}
          (BasicTerms _ _, Standard trs) -> case useTuples && strategy prob /= Innermost of 
                                             True -> return $ T.Failure $ NA {reason = "non-innermost rewriting and dependency tuples"}
                                             False -> do (_,ps) <- traverseNodes [] (roots ewdgSCC) [] Trs.empty
                                                         return $ T.Success (mkProof ps) (mkProbs ps)

              where traverseNodes pth ns dpss urs = do rs <- P.evalList' False [ traverse pth n_i dpss urs | n_i <- ns ]
                                                       return (List.find isJust [ ms | (ms,_) <- rs] >>= id, concatMap snd rs)

                    traverse pth n dpss urs = do (subsumed, rs) <- traverseNodes pth' (Graph.suc ewdgSCC n) dpss' urs'
                                                 (subsumed', proof) <- case subsumed of 
                                                                        (Just sp) -> do return $ (subsumed , PPSubsumedBy sp)
                                                                        Nothing   -> do wgcond <- weightGap dps_n (Trs.unions dpss') urs'
                                                                                        return $ ( if succeeded wgcond then Nothing else Just path
                                                                                                 , PPWeightGap wgcond)
                                                 return (subsumed', (path, proof) : rs)
                        where pth'  = pth ++ [n]
                              dps_n = nodeDPs ewdgSCC n
                              dpss' = dpss ++ [dps_n]
                              urs'  = nodeURs ewdgSCC n `Trs.union` urs
                              path  = Path pth' (dpss,dps_n) urs'

                    mkProof ps = WdgProof { computedPaths    = ps
                                          , computedGraph    = ewdg
                                          , computedGraphSCC = ewdgSCC
                                          , dependencyPairs  = wdps
                                          , usableRules      = allUsableRules
                                          , newSignature     = sig'
                                          , newVariables     = variables prob
                                          , containsNoEdgesEmptyUrs  = simple
                                          , tuplesUsed       = useTuples}

                    mkProbs ps | simple    = []
                               | otherwise = [(SN gpath, mk proof dpss dps urs) | (Path gpath (dpss,dps) urs, proof) <- ps, not $ isSubsumed proof]
                        where isSubsumed (PPSubsumedBy _) = True
                              isSubsumed _                = False
                              mk (PPWeightGap proof) dpss dps urs | succeeded proof = Problem { startTerms = startTerms'
                                                                                              , strategy   = strategy prob
                                                                                              , relation   = DP dps (Trs.unions $ urs : dpss)
                                                                                              , variables  = variables prob
                                                                                              , signature  = sig' }
                                                                  | otherwise       = Problem { startTerms = startTerms'
                                                                                              , strategy   = strategy prob
                                                                                              , relation   = Standard $ Trs.unions $ urs : dps : dpss
                                                                                              , variables  = variables prob
                                                                                              , signature  = sig' }
                              mk _                  _     _    _ = error "kabooom"

                    approx :+: _ :+: wgMatrixShape :+: wgDeg :+: wgMatrixDim :+: Nat wgMatrixBound :+: wgMatrixBits :+: wgMatrixCBits :+: wgUa :+: useTuples = T.transformationArgs inst
                    wgMatrixSize              = case wgMatrixBits of
                                                  Nothing -> N.Bound wgMatrixBound
                                                  Just (Nat b) -> N.Bits b

                    (startTerms', sig', wdps) = weakDependencyPairs useTuples prob

                    allUsableRules            = mkUsableRules wdps trs

                    ewdg                      = estimatedDependencyGraph approx sig' wdps trs

                    ewdgSCC                   = toSccGraph wdps trs ewdg

                    weightGap ds dss urs      = applyWeightGap ds usablePoss urs startTerms' sig' wgMatrixShape wgDeg wgMatrixDim wgMatrixSize wgMatrixCBits wgUa
                        where usablePoss      = usableArgs (strategy prob) dss urs

                    simple = null (Graph.edges ewdg) && Trs.isEmpty allUsableRules



-- dependency pairs and usable rules

instance (P.Processor sub) => PrettyPrintable (T.TProof Wdg sub) where
    pprint (T.UTProof _ p) = paragraph (unlines [ "This processor is only applicable to runtime-complexity analysis."
                                                , " We continue without dependency graph transformation." ])
                              $+$ pprint p

    pprint (T.TProof (NA r) _) = paragraph (unlines [ "This processor is not applicable to"
                                                    , r ++ "."
                                                    , "We abort." ])
    pprint proof@(T.TProof tp _) = block' "Transformation Details" [ppTrans]
                                   $+$ text ""
                                   $+$ if not simple 
                                       then block' "Sub-problems" [ppDetails]
                                       else PP.empty
        where printNodeId n = braces $ hcat $ intersperse (text ",") [text $ show i | i <- nodeSCC ewdgSCC n ]
              ppPathName (Path ns _ _) = hcat $ intersperse (text "->") [printNodeId n | n <- ns] 
              findPathProof gpth = T.findProof gpth proof
              findWGProof gpth = snd `liftM` List.find (\ (path, _) -> gpth == thePath path) (computedPaths tp)
              ewdgSCC = computedGraphSCC tp
              ewdg    = computedGraph tp
              sig     = newSignature tp
              vars    = newVariables tp
              simple  = containsNoEdgesEmptyUrs tp

              ppTrans = ppDPs $+$ text "" $+$ ppDG
                  where ppDPs = text "We have computed the following set of weak (innermost) dependency pairs:"
                                $+$ text ""
                                $+$ (indent $ pprintTrs pprule [ (n, fromJust (Graph.lab ewdg n)) | n <- Graph.nodes ewdg])
                                    where pprule (i,r) = text (show i) <> text ":" <+> pprint (r,sig,vars)

                        ppDG | containsNoEdgesEmptyUrs tp = text "The dependency graph contains no edges and the usable rules are empty."
                             | otherwise = paragraph "Following Dependency Graph (modulo SCCs) was computed. (Answers to subproofs are indicated to the right.)"
                                           $+$ text ""
                                           $+$ (indent $ printTree 60 ppNode ppLabel pTree)
                                           $+$ text ""
                             where ppNode _ n    = printNodeId n
                                   ppLabel pth _ = PP.brackets (centering 20 $ ppAns pth (findWGProof pth))
                                       where centering n d =  text $ take pre ss ++ s ++ take post ss
                                                 where s = show d
                                                       l = length s
                                                       ss = repeat ' '
                                                       pre = floor $ (fromIntegral (n - l) / 2.0 :: Double)
                                                       post = n - l - pre
                                   pTree = PPTree { pptRoots = roots ewdgSCC
                                                  , pptSuc = sortBy compareLabel . Graph.suc ewdgSCC}
                                   compareLabel n1 n2 = nodeSCC ewdgSCC n1 `compare` nodeSCC ewdgSCC n2

                        -- ppUargs = text "Following usable argument positions were computed:"
                        --           $+$ indent (pprint (usableArguments tp, sig))

              ppAns pth' Nothing                  = error $ "WDG.hs: findWGProof did not find path" ++ show pth'
              ppAns _    (Just (PPSubsumedBy _))  = text "inherited"
              ppAns pth' (Just (PPWeightGap p)) = case findPathProof pth' of
                                                      Just pp -> pprint $ pthAnswer p pp
                                                      Nothing -> text "NA"
                where pthAnswer tmi pp = if succeeded (answer tmi) then answerFromCertificate (max (certificate pp) (certificate tmi)) else answer pp

              ppDetails = vcat $ intersperse (text "") [ (text "*" <+> (underline (text "Path" <+> ppPathName path <> text ":" <+> ppAns (thePath path) (Just pathproof))
                                                                        $+$ text ""
                                                                        $+$ ppDetail path pathproof))
                                                         | (path, pathproof) <- sortBy comparePath $ computedPaths tp]
                  where comparePath (Path p1 _ _,_) (Path p2 _ _,_) = mkpath p1 `compare` mkpath p2
                            where mkpath p = [nodeSCC ewdgSCC n | n <- p]
                        ppDetail _    (PPSubsumedBy pth) = text "This path is subsumed by the proof of path" 
                                                           <+> ppPathName pth <> text "."
                        ppDetail path (PPWeightGap p) = (case (pathUsables path) of
                                                           (Trs []) -> text "The usable rules of this path are empty."
                                                           urs      -> text "The usable rules for this path are:"
                                                                      $+$ text ""
                                                                      $+$ (indent $ pprint (urs, sig, vars)))
                                                        $+$ text ""
                                                        $+$ text (if succeeded p
                                                                  then "The weightgap principle applies, using the following adequate RMI:" 
                                                                  else "The weight gap principle does not apply:")
                                                        $+$ indent (pprint p)
                                                        $+$ (case (pathUsables path) of
                                                               (Trs []) -> PP.empty
                                                               _        -> text "Complexity induced by the adequate RMI:" <+> pprint (answer p))
                                                        $+$ text ""
                                                        $+$ (case findPathProof (thePath path) of
                                                               Nothing -> text "We have not generated a proof for the resulting sub-problem."
                                                               Just pp -> text "We apply the sub-processor on the resulting sub-problem:"
                                                                         $+$ text ""
                                                                         $+$ pprint pp)

instance T.Verifiable WdgProof

instance (P.Processor sub) => Answerable (T.TProof Wdg sub) where
    answer = T.answerTProof ans
        where ans (NA _) _                                  = MaybeAnswer
              ans proof sps | containsNoEdgesEmptyUrs proof = answerFromCertificate $ certified (unknown, poly (Just 0))
                            | otherwise = answerFromCertificate $ certified (unknown, maximum $ (Poly $ Just 0) : [ mkUb sp | sp <- sps] ++ [tmiUb | tmiUb <- tmiUbs])
                  where mkUb (_,p) = case relation $ P.inputProblem p of
                                       Standard _ -> ub p
                                       _          -> assertLinear $ ub p
                        ub = upperBound . certificate
                        tmiUbs = map upperBound tmiCerts
                        tmiCerts = mapMaybe handlePathProof pathproofs
                        handlePathProof (PPSubsumedBy _) = Nothing
                        handlePathProof (PPWeightGap tmi) | succeeded tmi = Just $ certificate tmi
                                                          | otherwise     = Nothing
                        pathproofs = map snd $ computedPaths proof
                        assertLinear (Poly (Just n)) = Poly $ Just $ max 1 n
                        assertLinear (Poly Nothing)  = Poly Nothing
                        assertLinear e               = e
