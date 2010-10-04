{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeSynonymInstances #-}
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

module Tct.Method.Wdg where

import qualified Control.Monad.State.Lazy as State
import qualified Data.Graph.Inductive.Graph as Graph
import qualified Data.Graph.Inductive.Tree as GraphT
import qualified Data.Graph.Inductive.Query.DFS as GraphDFS
import qualified Data.List as List
import qualified Data.Maybe as Maybe
import Control.Monad (liftM)
import Control.Monad.Trans (liftIO)
import qualified Data.IntMap as IMap
import qualified Data.Set as Set
import Data.IntMap (IntMap)
import Data.List (partition)
import Data.Typeable 
import Data.Maybe (fromJust)
import Data.List (intersperse)
import qualified Qlogic.NatSat as N

import qualified Termlib.FunctionSymbol as F
import Termlib.Problem
import qualified Termlib.Term as Term
import Termlib.Term (Term)
import qualified Termlib.Rule as R
import Termlib.FunctionSymbol
import qualified Termlib.Signature as Sig
import Termlib.Rule (Rule)
import Termlib.FunctionSymbol (Signature)
import qualified Termlib.Trs as Trs
import Termlib.Trs (Trs(..), definedSymbols)
import qualified Termlib.Variable as V
import Termlib.Variable(Variables)
import Termlib.Utils

import Tct.Certificate
import Tct.Proof
import qualified Tct.Processor.Transformations as T
import qualified Tct.Processor.Standard as S
import qualified Tct.Processor as P
import Tct.Method.Matrix.NaturalMI (NaturalMI, NaturalMIKind(..), matrix)
import Tct.Processor.Args as A
import Tct.Processor.PPrint
import Tct.Processor.Args.Instances
import Text.PrettyPrint.HughesPJ hiding (empty)



----------------------------------------------------------------------
-- Proof object

data Path = Path { path    :: ([Trs],Trs)
                 , usables :: Trs }

type Graph = GraphT.Gr Rule ()

type SCCGraph = GraphT.Gr ([Int], Trs) ()

instance PrettyPrintable (SCCGraph, F.Signature, V.Variables) where
  pprint (g, sig, vars) = text "The nodes of the Dependency Graph (modulo SCCs) constitutes of the following nodes:"
                          $+$ (nest 1 $ vcat [printNode n | n <- Graph.nodes g])
                          $+$ text ""
                          $+$ text "Following edges were computed:"
                          $+$ (nest 1 $ vcat [printEdge e | e <- Graph.edges g])
      where printEdge (n1, n2) = printNodeId n1 <+> text "==>" <+> printNodeId n2
            printNode n = text "The node" <+> printNodeId n <+> text "constitutes of the following rules:" 
                          $+$ (nest 2 $ pprint (trs, sig, vars))
                where (_, trs) = fromJust $ Graph.lab g n
            printNodeId n = braces $ hcat $ intersperse (text ",") [text $ show i | i <- ids ]
                where (ids, _) = fromJust $ Graph.lab g n

data WdgProof = WdgProof { computedPaths     :: [(Path, Maybe (P.Proof (S.Processor NaturalMI)))]
                         , computedGraph     :: Graph
                         , computedGraphSCC  :: SCCGraph
                         , dependencyPairs   :: Trs
                         , usableRules       :: Trs
                         , newSignature      :: Signature
                         , containsNoEdges   :: Bool}
              | Inapplicable


instance PrettyPrintable WdgProof where 
    pprint Inapplicable = text "This processor is only applicable to runtime-complexity analysis"
    pprint proof = undefined

----------------------------------------------------------------------

-- Processor 
data Approximation = Edg deriving (Bounded, Ord, Eq, Typeable, Enum) 
instance Show Approximation where
    show Edg = "edg"

data Wdg = Wdg

wdgProcessor :: T.TransformationProcessor Wdg
wdgProcessor = T.transformationProcessor Wdg

wdg :: (P.ComplexityProcessor sub) => Approximation -> Bool -> Bool -> Bool -> P.InstanceOf sub -> T.Transformation Wdg sub
wdg approx weightgap = Wdg `T.calledWith` (approx :+: weightgap)

instance T.Transformer Wdg where
    name Wdg = "wdg"
    description Wdg = ["This processor implements path analysis based on (weak) Dependency Graphs."]

    type T.ArgumentsOf Wdg = Arg (EnumOf Approximation) :+: Arg (Bool)
    type T.ProofOf Wdg = WdgProof 
    instanceName _ = "Dependency Graph Analysis"
    arguments _ = opt { A.name = "approximation"
                      , A.defaultValue = Edg
                      , A.description = "specifies the employed dependency graph approximation"}
                  :+: 
                  opt { A.name = "weightgap"
                      , A.defaultValue = True
                      , A.description = "specifies whether the weightgap principle is used per path"}
    transform inst prob = 
        case (startTerms prob, relation prob) of 
          (BasicTerms ds cs, Standard trs) -> do let wg urs | useWG = return Nothing 
                                                           | otherwise = weightGap (N.Bits 4) Nothing $ wgProblem urs
                                                 ps <- P.evalList' useWG [ do wg urs >>= \ p -> return (pth, p) | pth@(Path _ urs) <- paths]
                                                 return $ T.Success (mkProof ps) (enumeration' $ mkSubProbs ps)
              where mkProof ps = WdgProof { computedPaths    = ps
                                          , computedGraph    = ewdg
                                          , computedGraphSCC = ewdgSCC
                                          , dependencyPairs  = wdps
                                          , usableRules      = mkUsableRules wdps trs
                                          , newSignature     = sig'
                                          , containsNoEdges  = null $ Graph.edges ewdg}
                    mkSubProbs ps | null $ Graph.edges ewdg = []
                                  | otherwise               = [subProblem p pth | (pth,p) <- ps]
                    (startTerms', sig', wdps) = weakDependencyPairs prob
                    ewdg = estimatedDependencyGraph approx sig' wdps trs
                    ewdgSCC = toSccGraph ewdg
                    paths = [ Path (ps,pm) (urs $ pm : ps) | (ps,pm) <- pathsFromSCCs ewdgSCC ]
                        where urs = mkUsableRules wdps . Trs.unions
                    wgProblem trs = Problem { startTerms = TermAlgebra
                                            , strategy   = Full
                                            , relation   = Standard trs
                                            , variables  = variables prob
                                            , signature  = sig' }
                    subProblem mp (Path (ps,pm) urs) = case mp of 
                                                         Nothing -> direct
                                                         Just p | succeeded p -> rp
                                                                | otherwise   -> direct
                        where direct = Problem { startTerms = TermAlgebra
                                               , strategy   = strategy prob
                                               , relation   = Standard $ Trs.unions $ pm : urs : ps
                                               , variables  = variables prob
                                               , signature  = sig' }
                              rp     = Problem { startTerms = TermAlgebra
                                               , strategy   = strategy prob
                                               , relation   = DP pm (Trs.unions $ urs : ps)
                                               , variables  = variables prob
                                               , signature  = sig' }
                    approx :+: useWG = T.transformationArgs inst


-- path analysis

toSccGraph :: Graph -> SCCGraph
toSccGraph gr = Graph.mkGraph nodes edges
    where nodes    = zip [1..] [(scc, Trs $ rules scc) | scc <- sccs]
          edges    = [ (n1, n2, ()) | (n1,(scc1,_)) <- nodes
                                    , (n2,(scc2,_)) <- nodes
                                    , n1 /= n2
                                    , isEdge scc1 scc2 ]
          isEdge scc1 scc2 = any id [ n2 `elem` Graph.suc gr n1 | n1 <- scc1, n2 <- scc2]
          sccs     = GraphDFS.scc gr
          rules scc = [Maybe.fromJust $ Graph.lab gr n | n <- scc]

pathsFromSCCs :: SCCGraph -> [([Trs], Trs)]
pathsFromSCCs gr = runMemoAction allPathsM
    where allPathsM = concat `liftM` mapM pathsM sources
              where sources = [n | n <- Graph.nodes gr, Graph.indeg gr n == 0]
          pathsM n = memo n $ do paths <- concat `liftM` mapM pathsM (Graph.suc gr n)
                                 return $ case paths of 
                                            [] -> [([],toTrs n)]
                                            _  -> ([],trs) : [ (trs : path,pm) | (path,pm) <- paths ] where trs = toTrs n
              where toTrs n = snd $ Maybe.fromJust $ Graph.lab gr n


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

weightGap :: P.SolverM m => N.Size -> Maybe Nat -> Problem -> m (Maybe (P.Proof (S.Processor NaturalMI)))
weightGap coefficientsize constraintbits prob | Trs.isDuplicating (strictTrs prob) = return $ Nothing
                                              | otherwise                          = Just `liftM` P.apply sli prob
    where sli = matrix Triangular (nat 1) coefficientsize constraintbits


-- approximations

estimatedDependencyGraph :: Approximation -> Signature -> Trs -> Trs -> Graph
estimatedDependencyGraph Edg = edg


edg :: F.Signature -> Trs.Trs -> Trs.Trs -> Graph
edg sig (Trs dps) trs = Graph.mkGraph nodes edges
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
                             (c, Term.Var x)                                    -> State.put (tail eqs, (c, x) : mergeqs) >> match'
          matchmerge = do eqs <- State.get
                          if null eqs 
                           then return True 
                           else do let (c, x) = head eqs
                                       eqs' = tail eqs
                                   case List.find ((== x) . snd) eqs' of
                                     Nothing     -> State.put eqs' >> matchmerge
                                     Just (d, y) -> case merge c d of
                                                     Nothing -> return False
                                                     Just e  -> State.put ((e, x) : List.delete (d, y) eqs') >> matchmerge
          merge Hole c                                         = Just c
          merge c Hole                                         = Just c
          merge (Fun f ss) (Fun g ts) | f /= g                 = Nothing
                                      | length ss /= length ts = Nothing
                                      | any (== Nothing) cs    = Nothing 
                                      | otherwise              = Just $ Fun f cs'
              where cs  = zipWith merge ss ts
                    cs' = map Maybe.fromJust cs


etcap :: [Term] -> Term -> GroundContext
etcap _ (Term.Var _)       = Hole
etcap lhss (Term.Fun f ts) = if any (match c) lhss then Hole else c
    where c = Fun f $ map (etcap lhss) ts

