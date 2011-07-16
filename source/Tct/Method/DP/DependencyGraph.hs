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

{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}

module Tct.Method.DP.DependencyGraph where


import qualified Data.Graph.Inductive.Graph as Graph
import qualified Data.Graph.Inductive.Tree as GraphT
import qualified Data.Graph.Inductive.Query.DFS as GraphDFS

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
import Text.PrettyPrint.HughesPJ hiding (empty, isEmpty)
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

data CDGNode = CongrNode { theSCC :: [(NodeId, DGNode)] } deriving (Show)

type CDG = DependencyGraph CDGNode (R.Rule, Int)

--------------------------------------------------------------------------------
-- Graph Inspection
--------------------------------------------------------------------------------


lookupNode :: DependencyGraph n e -> NodeId -> Maybe n
lookupNode = Graph.lab

lookupNode' :: DependencyGraph n e -> NodeId -> n
lookupNode' gr n = fromJust $ lookupNode gr n

roots :: DependencyGraph n e -> [NodeId]
roots gr = [n | n <- Graph.nodes gr, Graph.indeg gr n == 0]

leafs :: DependencyGraph n e -> [NodeId]
leafs gr = [n | n <- Graph.nodes gr, Graph.outdeg gr n == 0]

successors :: DependencyGraph n e -> NodeId -> [NodeId]
successors = Graph.suc

lsuccessors :: DependencyGraph n e -> NodeId -> [(NodeId, n, e)]
lsuccessors gr nde = [(n, lookupNode' gr n, e) | (n,e) <- Graph.lsuc gr nde]

withNodeLabels :: DependencyGraph n e -> [NodeId] -> [(NodeId, n)]
withNodeLabels gr ns = [(n,lookupNode' gr n) | n <- ns]

nodes :: DependencyGraph n e -> [NodeId]
nodes = Graph.nodes

lnodes :: DependencyGraph n e -> [(NodeId,n)]
lnodes = Graph.labNodes

-- rulesFromNode :: CDG -> Strictness -> NodeId -> [R.Rule]
-- rulesFromNode gr str n = case lookupNode gr n of 
--                             Nothing -> []
--                             Just cn -> [ r | (_, (str', r)) <- theSCC cn, str == str']

allRulesFromNode :: CDG -> NodeId -> [(Strictness, R.Rule)]
allRulesFromNode gr n = case lookupNode gr n of 
                            Nothing -> []
                            Just cn -> [ sr | (_, sr) <- theSCC cn]
                            
-- rulesFromNodes :: CDG -> Strictness -> [NodeId] -> Trs
-- rulesFromNodes gr str ns = Trs $ concatMap (rulesFromNode gr str) ns

allRulesFromNodes :: CDG -> [NodeId] -> [(Strictness, R.Rule)]
allRulesFromNodes gr ns = concatMap (allRulesFromNode gr) ns

congruence :: CDG -> NodeId -> [NodeId]
congruence gr n = fromMaybe [] ((map fst . theSCC) `liftM` Graph.lab gr n)


isEdgeTo :: DependencyGraph n e -> NodeId -> NodeId -> Bool
isEdgeTo g n1 n2 = n2 `elem` successors g n1 

isLEdgeTo :: Eq e => DependencyGraph n e -> NodeId -> e -> NodeId -> Bool
isLEdgeTo g n1 e n2 = n2 `elem` [n | (n, _, e2) <- lsuccessors g n1, e == e2]

--------------------------------------------------------------------------------
-- Estimated Dependency Graph
--------------------------------------------------------------------------------

data Approximation = Edg | Trivial deriving (Bounded, Ord, Eq, Typeable, Enum) 
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
          s@(Term.Fun f ts) `edgesTo` t = [ i | (i,ti) <- zip [1..] ts', ti `edgeToP` t] 
              where ts' | F.isCompound sig f = ts
                        | otherwise          = [s]
          (Term.Var _) `edgeToP` _    = False
          s            `edgeToP` t | approx == Edg = match (etcap lhss s) t 
                                                    && (any Term.isVariable rhss || match (etcap rhss t) s)
                                   | otherwise    = True
          sig = Prob.signature prob
          rs = Prob.trsComponents prob
          lhss = Trs.lhss rs
          rhss = Trs.rhss rs



--------------------------------------------------------------------------------
-- Congruence Dependency Graph
--------------------------------------------------------------------------------

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
          sccNode scc = CongrNode { theSCC = [ (n, fromJust $ lookupNode gr n) | n <- scc]}


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
pprintCWDGNode cwdg _ _ n = braces $ hcat $ punctuate (text ",") [text $ show i | i <- congruence cwdg n ]

pprintCWDG :: CDG -> F.Signature -> V.Variables -> ([NodeId] -> NodeId -> Doc) -> Doc
pprintCWDG cwdg sig vars ppLabel = printTree 60 ppNode ppLabel pTree
                                   $+$ text ""
                                   $+$ text "Here rules are as follows:"
                                   $+$ text ""
                                   $+$ (indent $ pprintLabeledRules sig vars rs )
    where ppNode _ n    = printNodeId n
          pTree = PPTree { pptRoots = sortBy compareLabel $ roots cwdg
                         , pptSuc = sortBy compareLabel . successors cwdg}
          compareLabel n1 n2 = congruence cwdg n1 `compare` congruence cwdg n2
          printNodeId = pprintCWDGNode cwdg sig vars 
          rs = sortBy compFst $ concatMap (\ (_, cn) -> [ (n, rule) | (n, (_, rule)) <- theSCC cn]) (Graph.labNodes cwdg)
            where (a1,_) `compFst` (a2,_) = a1 `compare` a2
          
instance PrettyPrintable (CDG, F.Signature, V.Variables) where 
  pprint (cwdg, sig, vars) = pprintCWDG cwdg sig vars (\ _ _ -> PP.empty)

pprintLabeledRules :: PrettyPrintable l => F.Signature -> V.Variables -> [(l,R.Rule)] -> Doc
pprintLabeledRules sig vars = pprintTrs pprule 
  where pprule (l,r) = pprint l <> text ":" <+> pprint (r, sig, vars)
