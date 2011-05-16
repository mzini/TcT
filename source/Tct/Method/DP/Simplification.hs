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

{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleInstances #-}

module Tct.Method.DP.Simplification where

import qualified Data.Set as Set
import Text.PrettyPrint.HughesPJ hiding (empty)

import qualified Termlib.FunctionSymbol as F
import qualified Termlib.Variable as V
import qualified Termlib.Problem as Prob
import qualified Termlib.Term as Term
import qualified Termlib.Rule as R
import Termlib.Rule (Rule (..))
import qualified Termlib.Trs as Trs
import Termlib.Trs (Trs(..))
import Termlib.Trs.PrettyPrint (pprintTrs)
import Termlib.Utils hiding (block)
import Termlib.Utils as Utils
import Data.Maybe (fromJust)

import qualified Tct.Processor.Transformations as T
import qualified Tct.Processor as P
import Tct.Processor.Args
import Tct.Processor.PPrint
import Tct.Method.DP.Utils 
import Tct.Method.DP.DependencyGraph
import qualified Data.Graph.Inductive.Graph as Graph


data RemoveLeaf = RemoveLeaf
data RemoveLeafProof = RLProof { leafs :: [(NodeId, Rule)] 
                               , graph    :: DG
                               , signature :: F.Signature
                               , variables :: V.Variables}
                     | Error DPError
                       
instance T.TransformationProof RemoveLeaf where
  answer = T.answerFromSubProof
  pprintProof _ _ (Error e) = pprint e
  pprintProof _ _ p         = text "We consider the dependency-graph"
                              $+$ text ""
                              $+$ indent (pprint (graph p, sig, vars))
                              $+$ text ""
                              $+$ text "The following rules are leafs in the dependency-graph and can be removed:"
                              $+$ text ""
                              $+$ indent (pprintTrs ppRule (leafs p))
     where vars = variables p                              
           sig = signature p
           ppRule (i, r) = text (show i) <> text ":" <+> pprint (r, sig, vars)
           
instance T.Transformer RemoveLeaf where
  name RemoveLeaf        = "removeleafs"
  description RemoveLeaf = ["Recursively removes all nodes leafs in the dependency-graph from the given problem"]
  
  type T.ArgumentsOf RemoveLeaf = Unit
  type T.ProofOf RemoveLeaf = RemoveLeafProof
  arguments RemoveLeaf = Unit
  transform _ prob | not $ Trs.isEmpty $ Prob.strictTrs prob = return $ T.NoProgress $ Error $ ContainsStrictRule
                   | null labLeafs  = return $ T.NoProgress proof
                   | otherwise      = return $ T.Progress proof (enumeration' [prob'])
        where labLeafs = map mkPair $ Set.toList $ computeLeafs initials Set.empty
                  where initials = [ n | n <- Graph.nodes wdg , Graph.outdeg wdg n == 0 ]
              ls = map snd labLeafs
              computeLeafs []     lfs = lfs
              computeLeafs (n:ns) lfs | n `Set.member` lfs = computeLeafs ns lfs
                                      | otherwise          = computeLeafs (ns++preds) lfs'
                   where preds = Graph.pre wdg n
                         sucs  = Graph.suc wdg n
                         lfs'  = if Set.fromList sucs `Set.isSubsetOf` lfs then Set.insert n lfs else lfs 
                                    
                    
              mkPair n = (n, snd $ fromJust $ lookupNode wdg n)
              wdg   = estimatedDependencyGraph Edg prob
              sig   = Prob.signature prob
              vars  = Prob.variables prob
              proof = RLProof { leafs = labLeafs
                              , graph = wdg
                              , signature = sig
                              , variables = vars }
              prob' = prob { Prob.strictDPs = Prob.strictDPs prob Trs.\\ Trs ls
                           , Prob.weakDPs   = Prob.weakDPs prob Trs.\\ Trs ls }
                

removeLeafProcessor :: T.TransformationProcessor RemoveLeaf P.AnyProcessor
removeLeafProcessor = T.transformationProcessor RemoveLeaf

removeLeafs :: T.TheTransformer RemoveLeaf
removeLeafs = RemoveLeaf `T.calledWith` ()
