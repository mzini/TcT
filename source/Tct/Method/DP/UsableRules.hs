{-# LANGUAGE FlexibleInstances #-}
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

module Tct.Method.DP.UsableRules where

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
import qualified Termlib.Problem as Prob
import qualified Termlib.Term as Term
import Termlib.Term (Term)
import qualified Termlib.Rule as R
import qualified Termlib.Signature as Sig
import Termlib.Rule (Rule)
import qualified Termlib.Trs as Trs
import Termlib.Trs.PrettyPrint (pprintTrs)
import Termlib.Trs (Trs(..))
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

mkUsableRules :: Trs -> Set.Set F.Symbol -> Trs -> Trs
mkUsableRules wdps ds trs = Trs $ usable (usableSymsRules $ rules wdps) (rules trs)
  where usableSymsTerm  t  = Set.filter (\ f -> f `Set.member` ds) $ Term.functionSymbols t
        usableSymsRules rs = Set.unions $ [usableSymsTerm (R.rhs r) | r <- rs]
        usable syms rs = case partition (\ r -> R.lhs r `rootFrom` syms) rs of 
                           ([],_)       -> []
                           (ur,remains) -> ur ++ usable (usableSymsRules ur `Set.union` syms) remains
        t `rootFrom` syms = case Term.root t of 
                              Right f -> f `Set.member` syms
                              Left _  ->  True


data UR = UR

data DPProof p = NonDPProblem 
               | DPProof p

data URProof = URProof

instance PrettyPrintable (DPProof URProof) where 
    pprint NonDPProblem = text "The input problem is not a DP-problem, we do not compute usable rules."
    pprint (DPProof _)  = text "We replace strict/weak-rules by the corresponding usable rules."

instance P.Processor sub => P.Answerable (T.TProof UR sub) where
    answer = T.answerTProof answer'
        where answer' _ [(_,p)] = P.answer p
              answer' _ _       = error "Usable rules received wrong number of subproofs"

instance P.Processor sub => PrettyPrintable (T.TProof UR sub) where
    pprint = T.prettyPrintTProof

instance T.Verifiable (DPProof URProof)

instance T.Transformer UR where 
    name UR = "Usable Rules"
    description UR = [ "This processor restricts the strict- and weak-rules to usable rules with"
                     , "respect to the dependency pairs."]
    type T.ArgumentsOf UR = Unit
    type T.ProofOf UR = DPProof URProof 
    arguments UR = Unit
    transform inst prob | not (Prob.isDPProblem prob) = return $ T.Failure NonDPProblem
                        | otherwise                 = return $ res
        where res | progressed = T.Success (DPProof URProof) (enumeration' [prob'])
                  | otherwise  = T.Failure (DPProof URProof)
              strs = Prob.strictTrs prob
              wtrs = Prob.weakTrs prob
              surs = mkUsableRules wdps ds strs
              wurs = mkUsableRules wdps ds wtrs
              progressed = size wurs < size wtrs || size surs < size strs
                  where size = length . Trs.rules
              ds   = Trs.definedSymbols (Prob.trsComponents prob)
              wdps = Prob.dpComponents prob
              prob' = prob { Prob.strictTrs = surs
                           , Prob.weakTrs   = wurs }


usableRulesProcessor :: T.TransformationProcessor UR P.AnyProcessor
usableRulesProcessor = T.transformationProcessor UR

usableRules :: (P.Processor sub) => P.InstanceOf sub -> P.InstanceOf (T.TransformationProcessor UR sub)
usableRules = T.transformationProcessor UR `T.calledWith` ()
