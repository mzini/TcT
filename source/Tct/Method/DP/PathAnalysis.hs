
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeSynonymInstances #-}

module Tct.Method.DP.PathAnalysis where

import Data.List (intersperse, sortBy)
import qualified Data.List as List
import Control.Monad (liftM)
import Control.Applicative ((<|>))
-- import Control.Monad.Trans (liftIO)
import Data.Maybe (fromJust, fromMaybe)
import Data.Either (partitionEithers)
import qualified Text.PrettyPrint.HughesPJ as PP 
import Text.PrettyPrint.HughesPJ hiding (empty)

import qualified Termlib.FunctionSymbol as F
import qualified Termlib.Problem as Prob
import qualified Termlib.Trs as Trs
import Termlib.Trs.PrettyPrint (pprintTrs)
import Termlib.Trs (Trs(..))
import qualified Termlib.Variable as V
import Termlib.Utils

import Tct.Certificate
import Tct.Method.DP.DependencyGraph
import qualified Tct.Processor.Transformations as T
import qualified Tct.Processor as P
import Tct.Processor (Answer(..), Answerable(..))
import Tct.Processor.Args as A
import Tct.Processor.PPrint
import Tct.Processor.Args.Instances ()
import Tct.Method.DP.Utils

----------------------------------------------------------------------
-- Proof objects

data Path = Path { thePath :: [NodeId] } deriving (Eq, Show)

data PathProof = PathProof { computedPaths   :: [Path]
                           , computedCongrDG :: CongrDG
                           , computedDG      :: DG
                           , subsumedBy      :: [(Path,[Path])]
                           , variables       :: V.Variables
                           , signature       :: F.Signature}

data PathAnalysis = PathAnalysis

instance T.Transformer PathAnalysis where
    name PathAnalysis        = "pathanalysis"
    description PathAnalysis = ["Pathanalysis"]
    type T.ArgumentsOf PathAnalysis = Unit
    type T.ProofOf PathAnalysis = DPProof PathProof
    arguments PathAnalysis = Unit
    transform _ prob | not $ Prob.isDPProblem prob = return $ T.Failure NonDPProblem
                     | otherwise                 = return $ res
        where res | progressed = T.Success p (enumeration [(thePath pth, prob') | (pth,prob') <- pathsToProbs ])
                  | otherwise  = T.Failure p
              edg  = estimatedDependencyGraph Edg prob
              cedg = toCongruenceGraph edg
              p = DPProof PathProof { computedPaths   = paths
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
                        strict_n = rulesFromNodes cedg StrictDP [n]
                        weak_n = rulesFromNodes cedg WeakDP [n]
                        weaks' = strict_n `Trs.union` weak_n `Trs.union` weaks
                        new | subsumed  = [Left  ( Path path, [Path $ path ++ [n'] | n' <- sucs ] )]
                            | otherwise = [Right ( Path path
                                                 , prob { Prob.strictDPs = strict_n, Prob.weakDPs = weaks} )]
                            where subsumed = not (null sucs) && Trs.isEmpty strict_n

              progressed = case paths of 
                             [pth] -> length spath > length sprob
                                 where Trs spath = rulesFromNodes cedg StrictDP (thePath pth)
                                       Trs sprob = Prob.strictDPs prob
                             _     -> True


instance (P.Processor sub) => Answerable (T.TProof PathAnalysis sub) where
    answer = T.answerTProof ans
        where ans NonDPProblem _ = MaybeAnswer
              ans (DPProof _) sps | all P.succeeded subproofs = P.answerFromCertificate $ certified (unknown, maximum $ (Poly $ Just 1) : upperbounds)
                                  | otherwise                 = P.MaybeAnswer
                  where subproofs = toList sps
                        upperbounds = [ upperBound $ P.certificate sp | sp <- subproofs]

instance (T.Verifiable (DPProof PathProof))

instance (P.Processor sub) => PrettyPrintable (T.TProof PathAnalysis sub) where
    pprint (T.UTProof NonDPProblem p) = 
        paragraph (unlines [ "This processor is only applicable to runtime-complexity analysis."
                           , " We continue without dependency graph transformation." ])
        $+$ pprint p

    pprint proof@(T.TProof (DPProof paproof) _) = block' "Transformation Details" [ppTrans]
                                                    $+$ text ""
                                                    $+$ block' "Sub-problems" [ppDetails]
        where printNodeId n = braces $ hcat $ intersperse (text ",") [text $ show i | i <- congruence cwdg n ]
              ppPathName (Path ns) = hcat $ intersperse (text "->") [printNodeId n | n <- ns] 
              cwdg = computedCongrDG paproof
              wdg = computedDG paproof
              findSubProof pth = T.findProof (thePath pth) proof

              ppMaybeAnswerOf pth = fromMaybe (text "?") (ppSpAns <|> ppSubsumed)
                  where ppSpAns    = pprint `liftM` P.answer `liftM` findSubProof pth
                        ppSubsumed = const (text "subsumed") `liftM` List.lookup pth (subsumedBy paproof)

              ppTrans = paragraph "Following congruence DG was used:"
                        $+$ text ""
                        $+$ (indent $ printTree 60 ppNode ppLabel pTree)
                        $+$ text ""
                        $+$ text "Here rules are as follows:"
                        $+$ text ""
                        $+$ (indent $ pprintTrs pprule [ (n, fromJust (lookupNode wdg n)) | n <- nodes wdg])
                            

                  where pprule (i,(_,r)) = text (show i) <> text ":" <+> pprint (r,signature paproof, variables paproof)
                        ppNode _ n    = printNodeId n
                        ppLabel pth _ = PP.brackets $ centering 20 $ ppMaybeAnswerOf (Path pth) 
                            where centering n d =  text $ take pre ss ++ s ++ take post ss
                                      where s = show d
                                            l = length s
                                            ss = repeat ' '
                                            pre = floor $ (fromIntegral (n - l) / 2.0 :: Double)
                                            post = n - l - pre
                        pTree = PPTree { pptRoots = sortBy compareLabel $ roots cwdg
                                       , pptSuc = sortBy compareLabel . successors cwdg}
                        compareLabel n1 n2 = congruence cwdg n1 `compare` congruence cwdg n2

              ppDetails = vcat $ intersperse (text "") [ (text "*" <+> (underline (text "Path" <+> ppPathName path <> text ":" <+> ppMaybeAnswerOf path)
                                                                        $+$ text ""
                                                                        $+$ ppDetail path))
                                                         | path <- sortBy comparePath $ computedPaths paproof]
                  where comparePath p1 p2 = mkpath p1 `compare` mkpath p2
                            where mkpath p = [congruence cwdg n | n <- thePath p]
                        ppDetail path = fromMaybe errMsg (ppsubsumed <|> ppsubproof)
                            where errMsg = text "CANNOT find proof of path" <+> ppPathName path <> text "." 
                                           <+> text "Propably computation has been aborted since some other path cannot be solved."
                                  ppsubsumed = do paths <- List.lookup path (subsumedBy paproof)
                                                  return $ (text "This path is subsumed by the proof of paths" 
                                                            <+> sep (intersperse (text ",") [ppPathName pth | pth <- paths])
                                                            <> text ".")
                                  ppsubproof = do subproof <- findSubProof path
                                                  return $ pprint subproof
--                                                           <+>  <> text "."
                        -- ppDetail path (PPWeightGap p) = (case (pathUsables path) of
                        --                                    (Trs []) -> text "The usable rules of this path are empty."
                        --                                    urs      -> text "The usable rules for this path are:"
                        --                                               $+$ text ""
                        --                                               $+$ (indent $ pprint (urs, sig, vars)))
                        --                                 $+$ text ""
                        --                                 $+$ text (if succeeded p
                        --                                           then "The weightgap principle applies, using the following adequate RMI:" 
                        --                                           else "The weight gap principle does not apply:")
                        --                                 $+$ indent (pprint p)
                        --                                 $+$ (case (pathUsables path) of
                        --                                        (Trs []) -> PP.empty
                        --                                        _        -> text "Complexity induced by the adequate RMI:" <+> pprint (answer p))
                        --                                 $+$ text ""
                        --                                 $+$ (case findPathProof (thePath path) of
                        --                                        Nothing -> text "We have not generated a proof for the resulting sub-problem."
                        --                                        Just pp -> text "We apply the sub-processor on the resulting sub-problem:"
                        --                                                  $+$ text ""
                        --                                                  $+$ pprint pp)


pathAnalysisProcessor :: T.TransformationProcessor PathAnalysis P.AnyProcessor
pathAnalysisProcessor = T.transformationProcessor PathAnalysis

pathAnalysis :: (P.Processor sub) => P.InstanceOf sub -> P.InstanceOf (T.TransformationProcessor PathAnalysis sub)
pathAnalysis = T.transformationProcessor PathAnalysis `T.calledWith` ()
-- wdg :: (P.Processor sub) => Approximation -> Bool -> NaturalMIKind -> Maybe Nat -> Nat -> N.Size -> Maybe Nat -> Bool -> Bool -> P.InstanceOf sub -> P.InstanceOf (T.TransformationProcessor Wdg sub)
-- wdg approx weightgap wgkind wgdeg wgdim wgsize wgcbits ua tuples = T.transformationProcessor Wdg `T.calledWith` (approx :+: weightgap :+: wgkind :+: wgdeg :+: wgdim :+: Nat (N.bound wgsize) :+: Nothing :+: wgcbits :+: ua :+: tuples)

-- instance T.Transformer Wdg where
--     name Wdg = "wdg"
--     description Wdg = ["This processor implements path analysis based on (weak) dependency graphs."]

--     type T.ArgumentsOf Wdg = (Arg (EnumOf Approximation)) :+: (Arg Bool) :+: (Arg (EnumOf NaturalMIKind)) :+: (Arg (Maybe Nat)) :+: (Arg Nat) :+: (Arg Nat) :+: (Arg (Maybe Nat)) :+: (Arg (Maybe Nat)) :+: (Arg Bool) :+: (Arg Bool)
--     type T.ProofOf Wdg = WdgProof 
--     instanceName _ = "Dependency Graph Analysis"
--     arguments _ = opt { A.name = "approximation"
--                       , A.defaultValue = Edg
--                       , A.description = "specifies the employed dependency graph approximation"}
--                   :+:
--                   opt { A.name = "weightgap"
--                       , A.defaultValue = True
--                       , A.description = "specifies whether the weightgap principle is used per path"}
--                   :+:
--                   opt { A.name        = "cert"
--                       , A.description = unlines [ "This argument specifies restrictions on the matrix-interpretation which induce polynomial growth of"
--                                                 , "the interpretation of the considered starting terms relative to their size for the weight gap condition."
--                                                 , "Here 'algebraic' refers to simple algebraic restrictions on matrices (in the current implementation,"
--                                                 , "they are simply restricted to triangular shape, i.e. matrices where coefficients in the lower-left"
--                                                 , "half below the diagonal are zero. Such matrix-interpretations induce polynomial derivational-complexity."
--                                                 , "If 'automaton' is given as argument, then criteria from the theory of weighted automata are used instead"
--                                                 , "(in the current implementation, the negations of the criteria EDA, and possibly IDA(n), in the case that"
--                                                 , "the flag 'degree' is set, are used)."
--                                                 , "If 'nothing' is given, then matrix-interpretations of all function symbols are unrestricted."
--                                                 , "Note that matrix interpretations produced with this option do not induce polynomial complexities in general."
--                                                 , "The default value is 'automaton'."
--                                                 ]
--                       , A.defaultValue = Automaton}
--                   :+:
--                   opt { A.name = "degree"
--                       , A.description = unlines [ "This argument ensures that the complexity induced by the matrix interpretation for the weight gap condition is bounded by a"
--                                                 , "polynomial of the given degree. Its internal effect is dictated by the value the argument 'cert' is set to."
--                                                 , "If it is set to 'algebraic', this restricts the number of non-zero entries in the diagonals of the matrices."
--                                                 , "If it is set to 'automaton', this set the paramter 'n' in the criterion 'not IDA(n)'."
--                                                 , "Finally, if it is set to 'unrestricted', the effect of setting the 'degree' argument is unspecified."
--                                                 ]
--                       , A.defaultValue = Nothing}
--                   :+:
--                   opt { A.name = "dim"
--                       , A.description = unlines [ "This argument specifies the dimension of the vectors and square-matrices appearing"
--                                                 , "in the matrix-interpretation for the weight gap condition."]
--                       , A.defaultValue = Nat 2 }
--                   :+:
--                   opt { A.name = "bound"
--                       , A.description = unlines [ "This argument specifies an upper-bound on coefficients appearing in the matrix"
--                                                 , "interpretation for the weight gap condition."]
--                       , A.defaultValue = Nat 3 }
--                   :+:
--                   opt { A.name = "bits"
--                       , A.description = unlines [ "This argument plays the same role as 'bound',"
--                                                 , "but instead of an upper-bound the number of bits is specified."
--                                                 , "This argument overrides the argument 'bound'." ]
--                       , A.defaultValue = Nothing }
--                   :+:
--                   opt { A.name = "cbits"
--                       , A.description = unlines [ "This argument specifies the number of bits used for intermediate results"
--                                                 , "computed for the matrix interpretation of the weight gap condition." ]
--                       , A.defaultValue = Nothing }
--                   :+:
--                   opt { A.name = "uargs"
--                       , A.description = unlines [ "This argument specifies whether usable arguments are computed (if applicable)"
--                                                 , "in order to relax the monotonicity constraints on the interpretation."]
--                       , A.defaultValue = True }
--                   :+:
--                   opt { A.name = "tuples"
--                       , A.description = unlines [ "Specifies whether Dependency-Tuples should be used for the innermost case."]
--                       , A.defaultValue = False }

--     transform inst prob =
--         case (startTerms prob, relation prob) of 
--           (TermAlgebra, _) -> return $ T.Failure $ NA {reason = "derivational complexity"}
--           (_, DP _ _) -> return $ T.Failure $ NA {reason = "DP problems"}
--           (_, Relative _ _) -> return $ T.Failure $ NA {reason = "relative problems"}
--           (BasicTerms _ _, Standard trs) -> case useTuples && strategy prob /= Innermost of 
--                                              True -> return $ T.Failure $ NA {reason = "non-innermost rewriting and dependency tuples"}
--                                              False -> do (_,ps) <- traverseNodes [] (roots ewdgSCC) [] Trs.empty
--                                                          return $ T.Success (mkProof ps) (mkProbs ps)

--               where traverseNodes pth ns dpss urs = do rs <- P.evalList' False [ traverse pth n_i dpss urs | n_i <- ns ]
--                                                        return (List.find isJust [ ms | (ms,_) <- rs] >>= id, concatMap snd rs)

--                     traverse pth n dpss urs = do (subsumed, rs) <- traverseNodes pth' (Graph.suc ewdgSCC n) dpss' urs'
--                                                  (subsumed', proof) <- case subsumed of 
--                                                                         (Just sp) -> do return $ (subsumed , PPSubsumedBy sp)
--                                                                         Nothing   -> do wgcond <- weightGap dps_n (Trs.unions dpss') urs'
--                                                                                         return $ ( if succeeded wgcond then Nothing else Just path
--                                                                                                  , PPWeightGap wgcond)
--                                                  return (subsumed', (path, proof) : rs)
--                         where pth'  = pth ++ [n]
--                               dps_n = nodeDPs ewdgSCC n
--                               dpss' = dpss ++ [dps_n]
--                               urs'  = nodeURs ewdgSCC n `Trs.union` urs
--                               path  = Path pth' (dpss,dps_n) urs'

--                     mkProof ps = WdgProof { computedPaths    = ps
--                                           , computedGraph    = ewdg
--                                           , computedGraphSCC = ewdgSCC
--                                           , dependencyPairs  = wdps
--                                           , usableRules      = allUsableRules
--                                           , newSignature     = sig'
--                                           , newVariables     = variables prob
--                                           , containsNoEdgesEmptyUrs  = simple
--                                           , tuplesUsed       = useTuples}

--                     mkProbs ps | simple    = []
--                                | otherwise = [(SN gpath, mk proof dpss dps urs) | (Path gpath (dpss,dps) urs, proof) <- ps, not $ isSubsumed proof]
--                         where isSubsumed (PPSubsumedBy _) = True
--                               isSubsumed _                = False
--                               mk (PPWeightGap proof) dpss dps urs | succeeded proof = Problem { startTerms = startTerms'
--                                                                                               , strategy   = strategy prob
--                                                                                               , relation   = DP dps (Trs.unions $ urs : dpss)
--                                                                                               , variables  = variables prob
--                                                                                               , signature  = sig' }
--                                                                   | otherwise       = Problem { startTerms = startTerms'
--                                                                                               , strategy   = strategy prob
--                                                                                               , relation   = Standard $ Trs.unions $ urs : dps : dpss
--                                                                                               , variables  = variables prob
--                                                                                               , signature  = sig' }
--                               mk _                  _     _    _ = error "kabooom"

--                     approx :+: _ :+: wgMatrixShape :+: wgDeg :+: wgMatrixDim :+: Nat wgMatrixBound :+: wgMatrixBits :+: wgMatrixCBits :+: wgUa :+: useTuples = T.transformationArgs inst
--                     wgMatrixSize              = case wgMatrixBits of
--                                                   Nothing -> N.Bound wgMatrixBound
--                                                   Just (Nat b) -> N.Bits b

--                     (startTerms', sig', wdps) = weakDependencyPairs useTuples prob

--                     allUsableRules            = mkUsableRules wdps trs

--                     ewdg                      = estimatedDependencyGraph approx sig' wdps trs

--                     ewdgSCC                   = toSccGraph wdps trs ewdg

--                     weightGap ds dss urs      = applyWeightGap ds usablePoss urs startTerms' sig' wgMatrixShape wgDeg wgMatrixDim wgMatrixSize wgMatrixCBits wgUa
--                         where usablePoss      = usableArgs (strategy prob) dss urs

--                     simple = null (Graph.edges ewdg) && Trs.isEmpty allUsableRules



-- -- dependency pairs and usable rules

-- instance (P.Processor sub) => PrettyPrintable (T.TProof Wdg sub) where
--     pprint (T.UTProof _ p) = paragraph (unlines [ "This processor is only applicable to runtime-complexity analysis."
--                                                 , " We continue without dependency graph transformation." ])
--                               $+$ pprint p

--     pprint (T.TProof (NA r) _) = paragraph (unlines [ "This processor is not applicable to"
--                                                     , r ++ "."
--                                                     , "We abort." ])
--     pprint proof@(T.TProof tp _) = block' "Transformation Details" [ppTrans]
--                                    $+$ text ""
--                                    $+$ if not simple 
--                                        then block' "Sub-problems" [ppDetails]
--                                        else PP.empty
--         where printNodeId n = braces $ hcat $ intersperse (text ",") [text $ show i | i <- nodeSCC ewdgSCC n ]
--               ppPathName (Path ns _ _) = hcat $ intersperse (text "->") [printNodeId n | n <- ns] 
--               findPathProof gpth = T.findProof gpth proof
--               findWGProof gpth = snd `liftM` List.find (\ (path, _) -> gpth == thePath path) (computedPaths tp)
--               ewdgSCC = computedGraphSCC tp
--               ewdg    = computedGraph tp
--               sig     = newSignature tp
--               vars    = newVariables tp
--               simple  = containsNoEdgesEmptyUrs tp

--               ppTrans = ppDPs $+$ text "" $+$ ppDG
--                   where ppDPs = text "We have computed the following set of weak (innermost) dependency pairs:"
--                                 $+$ text ""
--                                 $+$ (indent $ pprintTrs pprule [ (n, fromJust (Graph.lab ewdg n)) | n <- Graph.nodes ewdg])
--                                     where pprule (i,r) = text (show i) <> text ":" <+> pprint (r,sig,vars)

--                         ppDG | containsNoEdgesEmptyUrs tp = text "The dependency graph contains no edges and the usable rules are empty."
--                              | otherwise = paragraph "Following Dependency Graph (modulo SCCs) was computed. (Answers to subproofs are indicated to the right.)"
--                                            $+$ text ""
--                                            $+$ (indent $ printTree 60 ppNode ppLabel pTree)
--                                            $+$ text ""
--                              where ppNode _ n    = printNodeId n
--                                    ppLabel pth _ = PP.brackets (centering 20 $ ppAns pth (findWGProof pth))
--                                        where centering n d =  text $ take pre ss ++ s ++ take post ss
--                                                  where s = show d
--                                                        l = length s
--                                                        ss = repeat ' '
--                                                        pre = floor $ (fromIntegral (n - l) / 2.0 :: Double)
--                                                        post = n - l - pre
--                                    pTree = PPTree { pptRoots = roots ewdgSCC
--                                                   , pptSuc = sortBy compareLabel . Graph.suc ewdgSCC}
--                                    compareLabel n1 n2 = nodeSCC ewdgSCC n1 `compare` nodeSCC ewdgSCC n2

--                         -- ppUargs = text "Following usable argument positions were computed:"
--                         --           $+$ indent (pprint (usableArguments tp, sig))

--               ppAns pth' Nothing                  = error $ "WDG.hs: findWGProof did not find path" ++ show pth'
--               ppAns _    (Just (PPSubsumedBy _))  = text "inherited"
--               ppAns pth' (Just (PPWeightGap p)) = case findPathProof pth' of
--                                                       Just pp -> pprint $ pthAnswer p pp
--                                                       Nothing -> text "NA"
--                 where pthAnswer tmi pp = if succeeded (answer tmi) then answerFromCertificate (max (certificate pp) (certificate tmi)) else answer pp

--               ppDetails = vcat $ intersperse (text "") [ (text "*" <+> (underline (text "Path" <+> ppPathName path <> text ":" <+> ppAns (thePath path) (Just pathproof))
--                                                                         $+$ text ""
--                                                                         $+$ ppDetail path pathproof))
--                                                          | (path, pathproof) <- sortBy comparePath $ computedPaths tp]
--                   where comparePath (Path p1 _ _,_) (Path p2 _ _,_) = mkpath p1 `compare` mkpath p2
--                             where mkpath p = [nodeSCC ewdgSCC n | n <- p]
--                         ppDetail _    (PPSubsumedBy pth) = text "This path is subsumed by the proof of path" 
--                                                            <+> ppPathName pth <> text "."
--                         ppDetail path (PPWeightGap p) = (case (pathUsables path) of
--                                                            (Trs []) -> text "The usable rules of this path are empty."
--                                                            urs      -> text "The usable rules for this path are:"
--                                                                       $+$ text ""
--                                                                       $+$ (indent $ pprint (urs, sig, vars)))
--                                                         $+$ text ""
--                                                         $+$ text (if succeeded p
--                                                                   then "The weightgap principle applies, using the following adequate RMI:" 
--                                                                   else "The weight gap principle does not apply:")
--                                                         $+$ indent (pprint p)
--                                                         $+$ (case (pathUsables path) of
--                                                                (Trs []) -> PP.empty
--                                                                _        -> text "Complexity induced by the adequate RMI:" <+> pprint (answer p))
--                                                         $+$ text ""
--                                                         $+$ (case findPathProof (thePath path) of
--                                                                Nothing -> text "We have not generated a proof for the resulting sub-problem."
--                                                                Just pp -> text "We apply the sub-processor on the resulting sub-problem:"
--                                                                          $+$ text ""
--                                                                          $+$ pprint pp)

-- instance T.Verifiable WdgProof

-- instance (P.Processor sub) => Answerable (T.TProof Wdg sub) where
--     answer = T.answerTProof ans
--         where ans (NA _) _                                  = MaybeAnswer
--               ans proof sps | containsNoEdgesEmptyUrs proof = answerFromCertificate $ certified (unknown, poly (Just 0))
--                             | otherwise = answerFromCertificate $ certified (unknown, maximum $ (Poly $ Just 0) : [ mkUb sp | sp <- sps] ++ [tmiUb | tmiUb <- tmiUbs])
--                   where mkUb (_,p) = case relation $ P.inputProblem p of
--                                        Standard _ -> ub p
--                                        _          -> assertLinear $ ub p
--                         ub = upperBound . certificate
--                         tmiUbs = map upperBound tmiCerts
--                         tmiCerts = mapMaybe handlePathProof pathproofs
--                         handlePathProof (PPSubsumedBy _) = Nothing
--                         handlePathProof (PPWeightGap tmi) | succeeded tmi = Just $ certificate tmi
--                                                           | otherwise     = Nothing
--                         pathproofs = map snd $ computedPaths proof
--                         assertLinear (Poly (Just n)) = Poly $ Just $ max 1 n
--                         assertLinear (Poly Nothing)  = Poly Nothing
--                         assertLinear e               = e
