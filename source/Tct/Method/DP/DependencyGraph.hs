{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}

--------------------------------------------------------------------------------
-- | 
-- Module      :  Tct.Method.DP.DependencyGraph
-- Copyright   :  (c) Martin Avanzini <martin.avanzini@uibk.ac.at>, 
--                Georg Moser <georg.moser@uibk.ac.at>, 
--                Andreas Schnabl <andreas.schnabl@uibk.ac.at>,
-- License     :  LGPL (see COPYING)
--
-- Maintainer  :  Martin Avanzini <martin.avanzini@uibk.ac.at>
-- Stability   :  unstable
-- Portability :  unportable      
-- 

-- This module provides dependency graphs.
--------------------------------------------------------------------------------   


module Tct.Method.DP.DependencyGraph 
    (
     -- * Unified Graph Interface
     -- ** Datatypes
     DependencyGraph
     -- | @DependencyGraph n e@ is a Graph with node-labels @n@ and 
     -- edge-labels 'e'
    , Strictness (..)
    , NodeId
     -- | A node in the dependency graph. Most operations work on @NodeId@s. 
     -- Use @lookupNodeLabel@ to get the label of the node

     -- ** Operations
    , nodes
    -- | Returns the set of nodes. 
    , lnodes
    -- | Returns the set of nodes together with their labels. 
     , roots 
     -- | Returns the list of nodes without predecessor.
     , leafs
     -- | Returns the list of nodes without successor.
     , lookupNodeLabel
     -- | Returns the label of the given node, if present.
     , lookupNodeLabel'
     -- | Returns the label of the given node, if present. 
     -- Otherwise an exception is raised
     , withNodeLabels
     -- | List version of @lookupNodeLabel@.
     , withNodeLabels'
     -- | List version of @lookupNodeLabel'@.
     , successors
    -- | Returns the list of successors in a given node.
     , reachablesDfs
    -- | @reachable gr ns@ closes the list of nodes @ns@ under 
    -- the successor relation with respect to @ns@ in a depth-first manner
     , reachablesBfs
    -- | @reachable gr ns@ closes the list of nodes @ns@ under 
    -- the successor relation with respect to @ns@ in a breath-first manner
     , lsuccessors
    -- | Returns the list of successors in a given node, including their labels.
     , predecessors
    -- | Returns the list of predecessors in a given node.
     , lpredecessors
    -- | Returns the list of predecessors in a given node, including their labels.
    , isEdgeTo
    -- | @isEdgeTo dg n1 n2@ checks wheter @n2@ is a successor of @n1@ in 
    -- the dependency graph @dg@
    , isLEdgeTo
    -- | @isLEdgeTo dg n1 l n2@ checks wheter @n2@ is a successor of @n1@ in 
    -- the dependency graph @dg@, where the edge from @n1@ to @n2@ is 
    -- labeled by @l@.
    , subGraph
    -- | Computes the subgraph based on the given nodes.
    -- * Dependency Graph
    -- ** Datatype 
    , DG
    -- | The dependency graph.
    , DGNode
    -- | Nodes of the DG are labeled by rules and their strictness-annotation.
    , Approximation (..)

    -- ** Operations
    , estimatedDependencyGraph
    -- | @estimatedDependencyGraph approx prob@ 
    -- returns the estimated dependency-graph of a given problem @prob@ with 
    -- respect to the approximation @approx@.
     
    -- * Congruence Graph
    -- ** Datatype 
    , CDG
    -- | The congruence dependency graph.
    , CDGNode (..)

    -- ** Operations
    ,  toCongruenceGraph
    -- | Computes the congruence graph of a given dependency graph.
    , allRulesFromNode 
    -- | Returns the list of annotated rules of the given node.
    , allRulesFromNodes
    -- | List version of @allRulesFromNode@.
    , congruence
    -- | @congruence cdg n@ 
    -- returns the nodes from the original dependency graph (i.e., the one 
    -- given to @toCongruenceGraph@) that is denoted by the congruence-node @n@.
    , isCyclicNode
    -- | @isCyclicNode cdg n@ 
    -- returns @True@ iff there is an edge from a node in @congruence cdg n@
    -- to @congruence cdg n@ in the original dependency graph (i.e., the one 
    -- given to @toCongruenceGraph@).

    -- ** Utilities
    , pprintCWDGNode
      -- | @pprintCWDGNode cdg sig vars node@ is a default printer for the 
      -- CDG-node @node@. It shows the nodes of the dependency graph denoted by @node@  as a set.
    , pprintCWDG
      -- | Default pretty printer for CDGs. Prints the given CDG in a tree-like shape.
    , toGraphViz
      -- | translates 'DG' into a GraphViz graph.
    , saveGraphViz
      -- | output 'DG' as Svg.
    , graphvizShowDG
      -- | show a 'DG' in a GraphViz canvas.
    )
where

import qualified Data.Graph.Inductive.Graph as Graph
import qualified Data.Graph.Inductive.Tree as GraphT
import Data.Graph.Inductive.Query.DFS (dfs)
import qualified Data.Graph.Inductive.Query.DFS as GraphDFS
import Data.Graph.Inductive.Query.BFS (bfsn)

import qualified Data.GraphViz.Types.Monadic as GV
import qualified Data.GraphViz.Attributes as GVattribs
import Data.GraphViz.Types.Generalised
import qualified Data.GraphViz.Commands as GVcommands
import Data.Text.Lazy (pack)

import qualified Control.Monad.State.Lazy as State
import Data.List (delete, sortBy)
import qualified Data.List as List
import Control.Monad (liftM)
-- import Control.Monad.Trans (liftIO)
import Data.Typeable 
import Data.Maybe (fromJust, fromMaybe)

import qualified Termlib.FunctionSymbol as F
import qualified Termlib.Variable as V
import qualified Termlib.Problem as Prob
import Termlib.Problem (Problem)
import qualified Termlib.Term as Term
import Termlib.Term (Term)
import qualified Termlib.Rule as R
import qualified Termlib.Trs as Trs
import Termlib.Trs.PrettyPrint (pprintTrs)
import Text.PrettyPrint.HughesPJ hiding (empty, isEmpty, Str)
import qualified Text.PrettyPrint.HughesPJ as PP
import Termlib.Utils
import Tct.Processor.PPrint

--------------------------------------------------------------------------------
-- Dependency Graph Type
--------------------------------------------------------------------------------

type DependencyGraph n e = GraphT.Gr n e

type NodeId = Graph.Node

data Strictness = StrictDP | WeakDP deriving (Ord, Eq, Show)

type DGNode = (Strictness, R.Rule)
type DG = DependencyGraph DGNode Int

data CDGNode = CongrNode { theSCC :: [(NodeId, DGNode)]
                         , isCyclic :: Bool } deriving (Show)

type CDG = DependencyGraph CDGNode (R.Rule, Int)

--------------------------------------------------------------------------------
-- Graph Inspection
--------------------------------------------------------------------------------

nodes :: DependencyGraph n e -> [NodeId]
nodes = Graph.nodes

lnodes :: DependencyGraph n e -> [(NodeId,n)]
lnodes = Graph.labNodes

roots :: DependencyGraph n e -> [NodeId]
roots gr = [n | n <- Graph.nodes gr, Graph.indeg gr n == 0]

leafs :: DependencyGraph n e -> [NodeId]
leafs gr = [n | n <- Graph.nodes gr, Graph.outdeg gr n == 0]

lookupNodeLabel :: DependencyGraph n e -> NodeId -> Maybe n
lookupNodeLabel = Graph.lab

lookupNodeLabel' :: DependencyGraph n e -> NodeId -> n
lookupNodeLabel' gr n = fromJust $ lookupNodeLabel gr n

withNodeLabels :: DependencyGraph n e -> [NodeId] -> [(NodeId, Maybe n)]
withNodeLabels gr ns = [(n,lookupNodeLabel gr n) | n <- ns]

withNodeLabels' :: DependencyGraph n e -> [NodeId] -> [(NodeId, n)]
withNodeLabels' gr ns = [(n,lookupNodeLabel' gr n) | n <- ns]


successors :: DependencyGraph n e -> NodeId -> [NodeId]
successors = Graph.suc

reachablesBfs :: DependencyGraph n e -> [NodeId] -> [NodeId]
reachablesBfs = flip bfsn

reachablesDfs :: DependencyGraph n e -> [NodeId] -> [NodeId]
reachablesDfs = flip dfs

predecessors :: DependencyGraph n e -> NodeId -> [NodeId]
predecessors = Graph.pre

lsuccessors :: DependencyGraph n e -> NodeId -> [(NodeId, n, e)]
lsuccessors gr nde = [(n, lookupNodeLabel' gr n, e) | (n,e) <- Graph.lsuc gr nde]

lpredecessors :: DependencyGraph n e -> NodeId -> [(NodeId, n, e)]
lpredecessors gr nde = [(n, lookupNodeLabel' gr n, e) | (n,e) <- Graph.lpre gr nde]

isEdgeTo :: DependencyGraph n e -> NodeId -> NodeId -> Bool
isEdgeTo g n1 n2 = n2 `elem` successors g n1 

isLEdgeTo :: Eq e => DependencyGraph n e -> NodeId -> e -> NodeId -> Bool
isLEdgeTo g n1 e n2 = n2 `elem` [n | (n, _, e2) <- lsuccessors g n1, e == e2]

subGraph :: DependencyGraph n e -> [NodeId] -> DependencyGraph n e
subGraph g ns = Graph.delNodes (nodes g List.\\ ns) g

--------------------------------------------------------------------------------
-- Estimated Dependency Graph
--------------------------------------------------------------------------------

data Approximation = Edg -- ^ EDG*** approximation
                   | Trivial -- ^ Fully connected graph
                   deriving (Bounded, Ord, Eq, Typeable, Enum) 
instance Show Approximation where 
    show Edg     = "edg"
    show Trivial = "trivial"

estimatedDependencyGraph :: Approximation -> Problem -> DG
estimatedDependencyGraph approx prob = Graph.mkGraph ns es
    where ns = zip [1..] ([(StrictDP, r) | r <- Trs.rules $ Prob.strictDPs prob] 
                          ++ [(WeakDP, r) | r <- Trs.rules $ Prob.weakDPs prob])
          es = [ (n1, n2, i) | (n1,(_,l1)) <- ns
                             , (n2,(_,l2)) <- ns
                             , i <- R.rhs l1 `edgesTo` R.lhs l2] 
          (Term.Var _)      `edgesTo` _ = []
          s@(Term.Fun f ss) `edgesTo` t = [ i | (i,si) <- zip [1..] ss', si `edgeToP` t] 
              where ss' | F.isCompound sig f = ss
                        | otherwise          = [s]
          (Term.Var _) `edgeToP` _    = False
          s            `edgeToP` t | approx == Edg = match (etcap lhss s) t 
                                                    && (any Term.isVariable rhss 
                                                       || match (etcap rhss t) s)
                                   | otherwise    = True
          sig = Prob.signature prob
          rs = Prob.trsComponents prob
          lhss = Trs.lhss rs
          rhss = Trs.rhss rs



--------------------------------------------------------------------------------
-- Congruence Dependency Graph
--------------------------------------------------------------------------------

allRulesFromNode :: CDG -> NodeId -> [(Strictness, R.Rule)]
allRulesFromNode gr n = case lookupNodeLabel gr n of 
                            Nothing -> []
                            Just cn -> [ sr | (_, sr) <- theSCC cn]

allRulesFromNodes :: CDG -> [NodeId] -> [(Strictness, R.Rule)]
allRulesFromNodes gr ns = concatMap (allRulesFromNode gr) ns

congruence :: CDG -> NodeId -> [NodeId]
congruence cdg n = fromMaybe [] ((map fst . theSCC) `liftM` lookupNodeLabel cdg n)

isCyclicNode :: CDG -> NodeId -> Bool
isCyclicNode cdg n = isCyclic $ lookupNodeLabel' cdg n


toCongruenceGraph :: DG -> CDG
toCongruenceGraph gr = Graph.mkGraph ns es
    where ns    = zip [1..] [sccNode scc | scc <- GraphDFS.scc gr]
          es    = [ (n1, n2, i) | (n1, cn1) <- ns
                                 , (n2, cn2) <- ns
                                 , n1 /= n2
                                 , i <- cn1 `edgesTo` cn2 ]
          cn1 `edgesTo` cn2 = [ (r1, i) | (n1,(_,r1)) <- theSCC cn1
                              , (n, _, i) <- lsuccessors gr n1
                              , n `elem` map fst (theSCC cn2)]
          sccNode scc = CongrNode { theSCC = [ (n, fromJust $ lookupNodeLabel gr n) | n <- scc]
                                  , isCyclic = checkCyclic scc}
          checkCyclic [n] = n `elem` successors gr n
          checkCyclic _   = True

instance PrettyPrintable (DG, F.Signature, V.Variables) where 
  pprint (wdg, sig, vars) | isEmpty   = text "empty" 
                          | otherwise = vcat [ ppnode n rule $+$ text "" | (n, rule) <- rs]
    where isEmpty = length rs == 0
          rs = sortBy compFst [ (n, rule) | (n, (_, rule)) <- Graph.labNodes wdg]
            where (a1,_) `compFst` (a2,_) = a1 `compare` a2
          ppnode n rule = hang (text (show n) <> text ":" <+> pprule rule) 3 $ 
                            vcat [ arr i <+> pprule rule_m  <+> text ":" <> text (show m) 
                                 | (m,(_, rule_m),i) <- lsuccessors wdg n ]
          pprule r = pprint (r, sig, vars)
          arr i = text "-->_" <> text (show i)

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

pprintCWDGNode :: CDG -> F.Signature -> V.Variables -> NodeId -> Doc
pprintCWDGNode cwdg _ _ n = text (show n) <> (text ":") <> (braces $ hcat $ punctuate (text ",") [text $ show i | i <- congruence cwdg n ])

pprintCWDG :: CDG -> F.Signature -> V.Variables -> ([NodeId] -> NodeId -> Doc) -> Doc
pprintCWDG cwdg sig vars ppLabel = printTree 60 ppNode ppLabel pTree
                                   $+$ text ""
                                   $+$ text "Here dependency-pairs are as follows:"
                                   $+$ text ""
                                   $+$ pprintLabeledRules "Strict DPs" sig vars (rs StrictDP)
                                   $+$ pprintLabeledRules "WeakDPs DPs" sig vars (rs WeakDP)
    where ppNode _ n    = printNodeId n
          pTree = PPTree { pptRoots = sortBy compareLabel $ roots cwdg
                         , pptSuc = sortBy compareLabel . snub . successors cwdg}
          compareLabel n1 n2 = congruence cwdg n1 `compare` congruence cwdg n2
          printNodeId = pprintCWDGNode cwdg sig vars 
          rs strictness = sortBy compFst $ concatMap (\ (_, cn) -> [ (n, rule) | (n, (s, rule)) <- theSCC cn, s == strictness]) (Graph.labNodes cwdg)
            where (a1,_) `compFst` (a2,_) = a1 `compare` a2
          
instance PrettyPrintable (CDG, F.Signature, V.Variables) where 
  pprint (cwdg, sig, vars) = pprintCWDG cwdg sig vars (\ _ _ -> PP.empty)

pprintLabeledRules :: PrettyPrintable l => String -> F.Signature -> V.Variables -> [(l,R.Rule)] -> Doc
pprintLabeledRules _    _   _ [] = PP.empty
pprintLabeledRules name sig vars rs = text name <> text ":"
                                      $+$ indent (pprintTrs pprule rs)
  where pprule (l,r) = pprint l <> text ":" <+> pprint (r, sig, vars)


-- graphviz output of dgs

toGraphViz :: [(DG,F.Signature,V.Variables)] -> DotGraph NodeId
toGraphViz dgs = GV.digraph' $ mapM digraph $ zip [(1::Int)..] dgs
  where digraph (i,(dg,sig,vars)) = 
          do mapM_ sccToGV $ zip [(1::Int)..] (GraphDFS.scc dg)
             mapM_ edgesToGV nds
             GV.graphAttrs [GVattribs.toLabel $ "\\l" ++ show (pprintLabeledRules "Rules" sig vars lrules)]
          where nds   = nodes dg
                lrules = [(n,r) | (n,(_,r)) <- withNodeLabels' dg nds]
                sccToGV (j,scc) = GV.cluster (Str $ pack $ show i ++ "_" ++ show j) $ mapM nodesToGV $ withNodeLabels' dg scc
                nodesToGV (n,(strictness,_)) = GV.node n (attribs strictness)
                  where attribs StrictDP = [GVattribs.shape GVattribs.Circle]
                        attribs WeakDP   = [GVattribs.shape GVattribs.Circle, GVattribs.style GVattribs.dotted]
                edgesToGV n = mapM (\ (m,_,k) -> GV.edge n m [GVattribs.toLabel (show k)]) (lsuccessors dg n)
        
saveGraphViz :: [(DG,F.Signature,V.Variables)] -> FilePath -> IO FilePath
saveGraphViz dgs = GVcommands.runGraphvizCommand GVcommands.Dot (toGraphViz dgs) GVcommands.Svg
                
graphvizShowDG :: [(DG,F.Signature,V.Variables)] -> IO ()              
graphvizShowDG dgs = GVcommands.runGraphvizCanvas GVcommands.Dot (toGraphViz dgs) GVcommands.Gtk