{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
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
import Termlib.Trs (Trs(..))
import Termlib.Trs.PrettyPrint (pprintTrs)
import Text.PrettyPrint.HughesPJ hiding (empty)
import Termlib.Utils
import Tct.Processor.PPrint
--------------------------------------------------------------------------------
-- Dependency Graph Type
--------------------------------------------------------------------------------


type DependencyGraph n = GraphT.Gr n ()

type NodeId = Graph.Node

data Strictness = StrictDP | WeakDP deriving (Ord, Eq, Show)
type Node = (Strictness, R.Rule)
type DG = DependencyGraph Node

data CongrNode = CongrNode { theSCC :: [NodeId]
                           , weak :: Trs
                           , strict :: Trs }
type CongrDG = DependencyGraph CongrNode

--------------------------------------------------------------------------------
-- Graph Inspection
--------------------------------------------------------------------------------


lookupNode :: DependencyGraph n -> NodeId -> Maybe n
lookupNode = Graph.lab

roots :: DependencyGraph n -> [NodeId]
roots gr = [n | n <- Graph.nodes gr, Graph.indeg gr n == 0]

successors :: DependencyGraph n -> NodeId -> [NodeId]
successors = Graph.suc

nodes :: DependencyGraph n -> [NodeId]
nodes = Graph.nodes

rulesFromNodes :: CongrDG -> Strictness -> [NodeId] -> Trs
rulesFromNodes gr str ns = Trs.unions [ rulesFromNode n | n <- ns]
    where rulesFromNode n = case lookupNode gr n of 
                              Nothing -> Trs []
                              Just p | str == StrictDP -> strict p
                                     | otherwise      -> weak p

          -- nodeSCC :: CongrDG -> NodeId -> [NodeId]
          -- nodeSCC gr n = theSCC $ fromMaybe (error $ "node" ++ show n) (lookupNode gr n)

congruence :: CongrDG -> NodeId -> [NodeId]
congruence gr n = fromMaybe [] (theSCC `liftM` Graph.lab gr n)

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
          es = [ (n1, n2, ()) | (n1,(_,l1)) <- ns
                             , (n2,(_,l2)) <- ns
                             , R.rhs l1 `edgeTo` R.lhs l2] 
          s `edgeTo` t | approx == Trivial = True 
                       | approx == Edg     = any (\ si -> (match (etcap lhss si) t)) ss && invMatch
              where invMatch = if any Term.isVariable rhss then True else any (match $ etcap rhss t) ss
                    lhss = Trs.lhss rs
                    rhss = Trs.rhss rs
                    ss = filter ((== funroot t) . funroot) (sharpedSs s)
                    funroot x = case Term.root x of
                                  Left _  -> error "Variable root in funroot in Wdg.checkEdge"
                                  Right fun -> fun
                    sharpedSs (Term.Var _)                        = []
                    sharpedSs (Term.Fun f ss') | F.isMarked sig f = [Term.Fun f ss']
                                               | otherwise        = concatMap sharpedSs ss'
          sig = Prob.signature prob
          rs = Prob.trsComponents prob



--------------------------------------------------------------------------------
-- Congruence Dependency Graph
--------------------------------------------------------------------------------


toCongruenceGraph :: DG -> CongrDG
toCongruenceGraph gr = Graph.mkGraph ns es
    where ns    = zip [1..] [sccNode scc | scc <- sccs]
          es    = [ (n1, n2, ()) | (n1, CongrNode scc1 _ _) <- ns
                  , (n2, CongrNode scc2 _ _) <- ns
                  , n1 /= n2
                  , isEdge scc1 scc2 ]
          isEdge scc1 scc2 = any id [ n2 `elem` Graph.suc gr n1 | n1 <- scc1, n2 <- scc2]
          sccs             = GraphDFS.scc gr
          sccNode scc = CongrNode { theSCC    = scc
                                  , strict = Trs [ r | (StrictDP, r) <- dps]
                                  , weak   = Trs [ r | (WeakDP, r) <- dps] }
              where dps = [fromJust $ Graph.lab gr n | n <- scc]

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

pprintCWDGNode :: CongrDG -> F.Signature -> V.Variables -> NodeId -> Doc
pprintCWDGNode cwdg _ _ n = braces $ hcat $ punctuate (text ",") [text $ show i | i <- congruence cwdg n ]

pprintCWDG :: DG -> CongrDG -> F.Signature -> V.Variables -> ([NodeId] -> NodeId -> Doc) -> Doc
pprintCWDG wdg cwdg sig vars ppLabel = (indent $ printTree 60 ppNode ppLabel pTree)
                                       $+$ text ""
                                       $+$ text "Here rules are as follows:"
                                       $+$ text ""
                                       $+$ (indent $ pprintTrs pprule [ (n, fromJust (lookupNode wdg n)) | n <- nodes wdg])
    where pprule (i,(_,r)) = text (show i) <> text ":" <+> pprint (r, sig, vars)
          ppNode _ n    = printNodeId n
          pTree = PPTree { pptRoots = sortBy compareLabel $ roots cwdg
                         , pptSuc = sortBy compareLabel . successors cwdg}
          compareLabel n1 n2 = congruence cwdg n1 `compare` congruence cwdg n2
          printNodeId = pprintCWDGNode cwdg sig vars 