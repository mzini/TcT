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
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeSynonymInstances #-}

module Tct.Method.Wdg where

import qualified Control.Monad.State.Lazy as State
import qualified Data.Graph.Inductive.Graph as Graph
import qualified Data.Graph.Inductive.Tree as GraphT
import qualified Data.Graph.Inductive.Query.DFS as GraphDFS
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
-- Graph and Path Analysis

type Graph = GraphT.Gr Rule ()

data SCCNode = SCCNode { theSCC :: [Graph.Node]
                       , sccDPs :: Trs
                       , sccURs :: Trs
                       }

type SCCGraph = GraphT.Gr SCCNode ()

nodeDPs :: SCCGraph -> Graph.Node -> Trs
nodeDPs gr n = sccDPs $ fromJust $ Graph.lab gr n

nodeURs :: SCCGraph -> Graph.Node -> Trs
nodeURs gr n = sccURs $ fromJust $ Graph.lab gr n

nodeSCC :: SCCGraph -> Graph.Node -> [Graph.Node]
nodeSCC gr n = theSCC $ fromMaybe (error $ "node" ++ show n) (Graph.lab gr n)

roots :: (Graph.Graph gr) => gr a b -> [Graph.Node]
roots gr = [n | n <- Graph.nodes gr, Graph.indeg gr n == 0]


toSccGraph :: Trs -> Trs -> Graph -> SCCGraph
toSccGraph _ trs gr = Graph.mkGraph nodes edges
    where nodes    = zip [1..] [sccNode scc | scc <- sccs]
          edges    = [ (n1, n2, ()) | (n1, SCCNode scc1 _ _) <- nodes
                                    , (n2, SCCNode scc2 _ _) <- nodes
                                    , n1 /= n2
                                    , isEdge scc1 scc2 ]
          isEdge scc1 scc2 = any id [ n2 `elem` Graph.suc gr n1 | n1 <- scc1, n2 <- scc2]
          sccs             = GraphDFS.scc gr
          sccNode scc = SCCNode scc dps urs
              where dps = Trs [fromJust $ Graph.lab gr n | n <- scc]
                    urs = mkUsableRules dps trs

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
                         , containsNoEdgesEmptyUrs :: Bool}
              | NA { reason :: String }



----------------------------------------------------------------------
-- Processor

data Approximation = Edg | Trivial deriving (Bounded, Ord, Eq, Typeable, Enum) 
instance Show Approximation where 
    show Edg = "edg"
    show Trivial = "trivial"

data Wdg = Wdg

wdgProcessor :: T.TransformationProcessor Wdg
wdgProcessor = T.transformationProcessor Wdg

wdg :: (P.Processor sub) => Approximation -> Bool -> NaturalMIKind -> Nat -> N.Size -> Maybe Nat -> Bool -> Bool -> Bool -> P.InstanceOf sub -> T.Transformation Wdg sub
wdg approx weightgap wgkind wgdim wgsize wgcbits ua = Wdg `T.calledWith` (approx :+: weightgap :+: wgkind :+: wgdim :+: Nat (N.bound wgsize) :+: Nothing :+: wgcbits :+: ua)

instance T.Transformer Wdg where
    name Wdg = "wdg"
    description Wdg = ["This processor implements path analysis based on (weak) dependency graphs."]

    type T.ArgumentsOf Wdg = (Arg (EnumOf Approximation)) :+: (Arg Bool) :+: (Arg (EnumOf NaturalMIKind)) :+: (Arg Nat) :+: (Arg Nat) :+: (Arg (Maybe Nat)) :+: (Arg (Maybe Nat)) :+: (Arg Bool)
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
                  opt { A.name        = "kind"
                      , A.description = unlines [ "This argument specifies the particular shape of the matrix-interpretation for the weight gap condition."
                                                , "Here 'triangular' refers to matrices of triangular shape, i.e. matrices where coefficients in the lower-left half below the"
                                                , "diagonal are zero. Such matrix-interpretations induce polynomial derivational-complexity." 
                                                , "If 'constructor' is given as argument, then defined symbols are interpreted using unrestricted"
                                                , "matrix-interpretations, whereas constructors are interpreted by interpretations of triangular shape."
                                                , "Such matrix-interpretations induce polynomial upper-bounds on the runtime-complexity."
                                                , "If 'unrestricted' is given, then matrix-interpretations of all function symbols are unrestricted."
                                                , "Those induce exponentially bounded derivational-complexity."
                                                , "Finally 'default' is 'constructor' for runtime-, and 'triangular' for derivational-complexity analysis."
                                                ]
                      , A.defaultValue = Default}
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
--                   :+:
--                   opt { A.name = "uargs"
--                       , A.description = unlines [ "This argument specifies the approximation used for calculating the usable argument"
--                                                 , "positions for the weight gap condition."
--                                                 , "Here 'byFunctions' refers to just looking at defined function symbols, while 'byCap' refers"
--                                                 , "to using a tcap-like function." ]
--                       , A.defaultValue = UArgByCap }
    transform inst prob =
        case (startTerms prob, relation prob) of 
          (TermAlgebra, _) -> return $ T.Failure $ NA {reason = "derivational complexity"}
          (_, DP _ _) -> return $ T.Failure $ NA {reason = "DP problems"}
          (_, Relative _ _) -> return $ T.Failure $ NA {reason = "relative problems"}
          (BasicTerms _ _, Standard trs) -> do (_,ps) <- traverseNodes [] (roots ewdgSCC) [] Trs.empty
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
                                          , containsNoEdgesEmptyUrs  = simple}

                    mkProbs ps | simple    = []
                               | otherwise = [(SN gpath, mk proof dpss dps urs) | (Path gpath (dpss,dps) urs, proof) <- ps, not $ isSubsumed proof]
                        where isSubsumed (PPSubsumedBy _) = True
                              isSubsumed _                = False
                              mk (PPWeightGap proof) dpss dps urs | succeeded proof = Problem { startTerms = startTerms'
                                                                                              , strategy   = strategy prob
                                                                                              , relation   = DP (Trs.unions $ dps : dpss) urs
                                                                                              , variables  = variables prob
                                                                                              , signature  = sig' }
                                                                  | otherwise       = Problem { startTerms = startTerms'
                                                                                              , strategy   = strategy prob
                                                                                              , relation   = Standard $ Trs.unions $ urs : dps : dpss
                                                                                              , variables  = variables prob
                                                                                              , signature  = sig' }
                              mk _                  _     _    _ = error "kabooom"

                    approx :+: _ :+: wgMatrixShape :+: wgMatrixDim :+: Nat wgMatrixBound :+: wgMatrixBits :+: wgMatrixCBits :+: wgUa = T.transformationArgs inst
                    wgMatrixSize              = case wgMatrixBits of
                                                  Nothing -> N.Bound wgMatrixBound
                                                  Just (Nat b) -> N.Bits b

                    (startTerms', sig', wdps) = weakDependencyPairs prob

                    allUsableRules            = mkUsableRules wdps trs

                    ewdg                      = estimatedDependencyGraph approx sig' wdps trs

                    ewdgSCC                   = toSccGraph wdps trs ewdg

                    weightGap ds dss urs      = applyWeightGap ds usablePoss urs startTerms' sig' wgMatrixShape wgMatrixDim wgMatrixSize wgMatrixCBits wgUa
                        where usablePoss      = usableArgs (strategy prob) dss urs

                    simple = null (Graph.edges ewdg) && Trs.isEmpty allUsableRules



-- dependency pairs and usable rules

weakDependencyPairs :: Problem -> (StartTerms, Signature, Trs)
weakDependencyPairs prob = 
    case (startTerms prob, relation prob) of 
      (BasicTerms ds cs, Standard trs) -> (BasicTerms dssharp cs, sig, wdps)
          where ((wdps,dssharp),sig) = flip Sig.runSignature (signature prob) $ 
                                       do dps <- weakDPs (strategy prob) trs 
                                          ds' <- Set.fromList `liftM` (mapM markSymbol $ Set.elems ds)
                                          return (dps, ds')
      _                -> error "Wdp.weakDependencyPairs called with non-basic terms"

markSymbol :: Symbol -> SignatureMonad Symbol
markSymbol f = do fa <- getAttributes f 
                  maybeFresh fa{symIsMarked = True}

-- AS: MA and GM say that not leaving out unary compound symbols obviously does not make any difference at all for the currently used techniques
--     AS does not know about this, however, not leaving that symbol does no harm, either
--     GM wants that these facts are explicitly written down as a comment in the code
weakDPs :: Strategy -> Trs -> SignatureMonad Trs
weakDPs strat trs = Trs `liftM` (mapM mk $ zip (rules trs) ([0..] :: [Int]))
  where ds = definedSymbols trs 
        mk (rule,i) = do lhs' <- mrk $ R.lhs rule
                         rhs' <- mkRhs i $ R.rhs rule
                         return $ R.fromPair (lhs',rhs')
        mkRhs i t   = fromSubterms $ gatherSubterms p t
          where p (Left _)  = not (strat == Innermost)
                p (Right f) = f `Set.member` ds
                fromSubterms ts = do c <- fresh (defaultAttribs ("c_" ++ show i) (length ts)) {symIsCompound = True}
                                     ts' <- mapM mrk ts
                                     return $ Term.Fun c ts'
                gatherSubterms f v@(Term.Var x)      | f (Left x)    = [v]
                                                     | otherwise     = []
                gatherSubterms f s@(Term.Fun sym ss) | f (Right sym) = [s]
                                                     | otherwise     = concatMap (gatherSubterms f) ss
        mrk v@(Term.Var _) = return $ v
        mrk (Term.Fun f ts) = do f' <- markSymbol f
                                 return $ Term.Fun f' ts

mkUsableRules :: Trs -> Trs -> Trs
mkUsableRules wdps trs = Trs $ usable (usableSymsRules $ rules wdps) (rules trs)
  where ds = definedSymbols trs 
        usableSymsTerm  t  = Set.filter (\ f -> f `Set.member` ds) $ Term.functionSymbols t
        usableSymsRules rs = Set.unions $ [usableSymsTerm (R.rhs r) | r <- rs]
        usable syms rs = case partition (\ r -> R.lhs r `rootFrom` syms) rs of 
                           ([],_)       -> []
                           (ur,remains) -> ur ++ usable (usableSymsRules ur `Set.union` syms) remains
        t `rootFrom` syms = case Term.root t of 
                              Right f -> f `Set.member` syms
                              Left _  ->  True

-- approximations

estimatedDependencyGraph :: Approximation -> Signature -> Trs -> Trs -> Graph
estimatedDependencyGraph Edg sig (Trs dps) trs = Graph.mkGraph nodes edges
    where nodes = zip [1..] dps
          edges = [ (n1, n2, ()) | (n1,l1) <- nodes
                                 , (n2,l2) <- nodes
                                 , R.rhs l1 `edgeTo` R.lhs l2] 
          s `edgeTo` t = any (\ si -> (match (etcap lhss si) t)) ss && invMatch
              where invMatch = if any Term.isVariable rhss then True else any (match $ etcap rhss t) ss
                    lhss = Trs.lhss trs
                    rhss = Trs.rhss trs
                    ss = filter ((== funroot t) . funroot) (sharpedSs s)
                    funroot x = case Term.root x of
                                  Left _  -> error "Variable root in funroot in Wdg.checkEdge"
                                  Right fun -> fun
                    sharpedSs (Term.Var _)                        = []
                    sharpedSs (Term.Fun f ss') | F.isMarked sig f = [Term.Fun f ss']
                                               | otherwise        = concatMap sharpedSs ss'
estimatedDependencyGraph Trivial _ (Trs dps) _ = Graph.mkGraph nodes edges
    where nodes = zip [1..] dps
          edges = [ (n1, n2, ()) | (n1,_) <- nodes
                                 , (n2,_) <- nodes ]
-- utilities

data GroundContext = Hole | Fun F.Symbol [GroundContext]
  deriving Eq

match :: GroundContext -> Term -> Bool
match c t = State.evalState match' ([(c, t)], [])
    where match' = do (eqs, mergeqs) <- State.get
                      if null eqs 
                       then return $ State.evalState matchmerge mergeqs 
                       else case head eqs of
                             (Hole, _)                                          -> State.put (tail eqs, mergeqs) >> match'
                             (Fun f ss, Term.Fun g ts) | f /= g                 -> return False
                                                       | length ss /= length ts -> return False
                                                       | otherwise              -> State.put (zip ss ts ++ tail eqs, mergeqs) >> match'
                             (c', Term.Var x)                                   -> State.put (tail eqs, (c', x) : mergeqs) >> match'
          matchmerge = do eqs <- State.get
                          if null eqs 
                           then return True 
                           else do let (c', x) = head eqs
                                       eqs' = tail eqs
                                   case List.find ((== x) . snd) eqs' of
                                     Nothing     -> State.put eqs' >> matchmerge
                                     Just (d, y) -> case merge c' d of
                                                     Nothing -> return False
                                                     Just e  -> State.put ((e, x) : delete (d, y) eqs') >> matchmerge
          merge Hole c'                                        = Just c'
          merge c' Hole                                        = Just c'
          merge (Fun f ss) (Fun g ts) | f /= g                 = Nothing
                                      | length ss /= length ts = Nothing
                                      | any (== Nothing) cs    = Nothing 
                                      | otherwise              = Just $ Fun f cs'
              where cs  = zipWith merge ss ts
                    cs' = map fromJust cs


etcap :: [Term] -> Term -> GroundContext
etcap _ (Term.Var _)       = Hole
etcap lhss (Term.Fun f ts) = if any (match c) lhss then Hole else c
    where c = Fun f $ map (etcap lhss) ts



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
