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

module Tct.Method.DP.UsableRules where

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
import Termlib.Trs.PrettyPrint (pprintNamedTrs)
import Termlib.Utils hiding (block)
import Termlib.Utils as Utils

import qualified Tct.Processor.Transformations as T
import qualified Tct.Processor as P
import Tct.Processor.Args as A
import Tct.Processor.PPrint
import Tct.Method.DP.Utils 

mkUsableRules :: Prob.Problem -> Trs -> Trs
mkUsableRules prob trs = trs `restrictTo` Set.unions [decendants f | f <- ds
                                                                   , Rule _ r <- Trs.rules $ Prob.dpComponents prob
                                                                   , f `Set.member` Term.functionSymbols r ]
  where Trs rs `restrictTo` roots = Trs $ [ rule | rule <- rs, let Right f = Term.root (R.lhs rule) in f `Set.member` roots ]
        decendants f = reachable step [f] Set.empty
          where step f' = Set.fromList [ g | g <- ds
                                           , Rule l r <- Trs.rules trss
                                           , Term.root l == Right f'
                                           , g `Set.member` Term.functionSymbols r ]
        reachable _     []     visited                          = visited
        reachable nexts (f:fs) visited | f `Set.member` visited = reachable nexts fs visited
                                       | otherwise              = reachable nexts (fs' ++ fs) (Set.insert f visited)
                                            where fs' = Set.toList $ nexts f
                                                  
        ds = Set.toList $ Trs.definedSymbols trss
        trss = Prob.trsComponents prob


data UR = UR

data URProof = URProof { usableStrict :: Trs
                       , usableWeak   :: Trs
                       , signature    :: F.Signature
                       , variables    :: V.Variables
                       , progressed   :: Bool}
               | Error DPError

instance PrettyPrintable URProof where 
    pprint p@URProof {} | null allUrs     = text "No rule is usable."
                        | progressed p    = text "We replace strict/weak-rules by the corresponding usable rules:"
                                            $+$ text ""
                                            $+$ indent (ppTrs "Strict Usable Rules" (usableStrict p)
                                                       $+$ ppTrs "Weak Usable Rules" (usableWeak p))
                        | otherwise       = text "All rules are usable."
        where ppTrs  = pprintNamedTrs (signature p) (variables p)
              allUrs = Trs.rules (usableStrict p) ++ Trs.rules (usableWeak p)
    pprint (Error e)                    = pprint e

instance T.TransformationProof UR where
    answer = T.answerFromSubProof
    pprintProof _ _ = pprint


instance T.Transformer UR where 
    name UR = "usablerules"
    description UR = [ "This processor restricts the strict- and weak-rules to usable rules with"
                     , "respect to the dependency pairs."]
    type T.ArgumentsOf UR = Unit
    type T.ProofOf UR = URProof 
    arguments UR = Unit
    transform _ prob | not (Prob.isDPProblem prob) = return $ T.NoProgress $ Error NonDPProblemGiven
                     | otherwise                 = return $ res
        where res | progr     = T.Progress ursproof (enumeration' [prob'])
                  | otherwise = T.NoProgress ursproof
              strs = Prob.strictTrs prob
              wtrs = Prob.weakTrs prob
              surs = mkUsableRules prob strs
              wurs = mkUsableRules prob wtrs
              progr = size wurs < size wtrs || size surs < size strs
                  where size = length . Trs.rules
              ursproof = URProof { usableStrict = surs
                                 , usableWeak  = wurs
                                 , signature   = Prob.signature prob
                                 , variables   = Prob.variables prob
                                 , progressed  = progr }
              prob' = prob { Prob.strictTrs = surs
                           , Prob.weakTrs   = wurs }


usableRulesProcessor :: T.TransformationProcessor UR P.AnyProcessor
usableRulesProcessor = T.transformationProcessor UR

usableRules :: T.TheTransformer UR
usableRules = UR `T.calledWith` ()
