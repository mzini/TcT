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
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ExistentialQuantification #-}

module Tct.Method.Relative where

import Text.PrettyPrint.HughesPJ
import Control.Monad (liftM)
import Termlib.Problem
import Termlib.Utils (PrettyPrintable(..))
import qualified Termlib.Trs as Trs
import Termlib.Trs ((\\))
import Termlib.Rule (Rule)
import qualified Tct.Processor.Standard as S
import qualified Tct.Processor as P
import Tct.Processor (Answerable (..), Verifiable(..), succeeded)
import Tct.Processor.Args hiding (name, description, synopsis)
import qualified Tct.Processor.Args as A
import Tct.Processor.Args.Instances
import Tct.Certificate (upperBound, unknown, certified, mult, compose, poly, add, iter, constant)
-- Proof Objects

data RelativeProof p sub = RelativeProof (P.PartialProof (P.ProofOf p)) (P.Proof sub)
                         | RelativeDirect String (P.Proof sub)
                         | RelativeEmpty 

removedRules :: RelativeProof p sub -> [Rule]
removedRules (RelativeProof rp _) = P.ppRemovable rp
removedRules _= []

-- MA:TODO: think about applicable predicate
appliesTo :: Problem -> (Bool, String)
appliesTo prob = (not isRcProblem && not isDpProblem && weakNoneSizeIncreasing, reason)
  where isDpProblem            = case relation prob of {DP{} -> True; _ -> False}
        isRcProblem            = case startTerms prob of {TermAlgebra{} -> False; _ -> True}
        weakNoneSizeIncreasing = Trs.isEmpty weak || Trs.isNonSizeIncreasing weak
          where weak = weakTrs prob
        reason | isDpProblem = "the relative processor is not implemented for DP problems" 
               | isRcProblem = "the relative processor is not applicable to runtime complexity problems"
               | otherwise   = "the weak TRS is size-increasing"                   

instance (Answerable (P.ProofOf p), Answerable (P.ProofOf sub)) => Answerable (RelativeProof p sub) where 
    answer (RelativeProof relp subp) = P.answerFromCertificate $ certified (unknown, res)
    -- note that weak trs is guarded to be non-size-increasing
      where res = combine (upperBound $ P.certificate relp) (upperBound $ P.certificate subp)
            r       = Trs.fromRules $ P.ppRemovable relp
            s       = strictTrs $ P.inputProblem subp
--            w       = weakTrs   $ P.inputProblem subp 
            sizeIncreasingR = Trs.isSizeIncreasing r
            sizeIncreasingS = Trs.isSizeIncreasing s
            combine ubRModS ubS | not sizeIncreasingS
                                  && not sizeIncreasingR  = ubRModS `mult` ubS
                                | not sizeIncreasingS    = ubRModS `mult` (ubS `compose` (poly (Just 1) `add` ubRModS))
                                | otherwise            = ubRModS `mult` (ubS `iter` ubRModS)
    answer (RelativeDirect _ subp) = P.answer subp
    answer RelativeEmpty = P.answerFromCertificate $ certified (constant, constant)

instance Verifiable (P.ProofOf sub) => Verifiable (RelativeProof p sub) where 
    verify _ (RelativeProof _ subp) = verify (P.inputProblem subp) (P.result subp)
    verify _ _                        = P.verifyOK

instance (P.Processor p, P.Processor sub) => PrettyPrintable (RelativeProof p sub) where
  pprint (RelativeProof pp subp) = 
    case succeeded pp of
      True  -> text "First we apply the relative processor:"
              $+$ pprint pp
              $+$ text ""
              $+$ text "Next, we apply the subprocessor:"
              $+$ pprint subp
      False -> text "The relative processor was not successful. We apply the subprocessor directly"
              $+$ pprint subp
  pprint (RelativeDirect reason subp) = text ("We apply the given subprocessor directly since " ++ reason)
                                        $+$ pprint subp
  pprint RelativeEmpty = text "The strict component of the problem is empty"                                 
-- Relative Processor

data RelativeProcessor p sub = RelativeProcessor

instance (P.Processor sub, P.Processor p) => S.Processor (RelativeProcessor p sub) where
  name RelativeProcessor = "relative"
  description _ = ["The processor 'relative p1 p2' first tries to remove rules using processor p1, and then continues with processor p2 on the resulting subproblem."] 
  type S.ProofOf (RelativeProcessor p sub) = RelativeProof p sub
  type S.ArgumentsOf (RelativeProcessor p sub) = Arg (Proc p) :+: Arg (Proc sub)
  arguments _ = arg { A.name = "relativeprocessor"
                    , A.description = "The processor that is used to \"remove\" rules" }
                :+: arg { A.name = "subprocessor"
                        , A.description = "The processor that is applied after removing rules"}

  solve inst prob | Trs.isEmpty (strictTrs prob) = return $ RelativeEmpty 
                  | not applicable = RelativeDirect reason `liftM` P.apply subproc prob
                  | otherwise = 
           do res <- P.solvePartial remproc prob
              let removed = Trs.fromRules (P.ppRemovable res)
                  subprob = case relation prob of
                                       Standard strict      -> prob'{relation = Standard $ strict \\ removed}
                                       Relative strict weak -> prob'{relation = Relative (strict \\ removed) weak}
                                       DP       _      _    -> error "Relative Rule Removal inapplicable for DP problems"
              subproof <- P.apply subproc subprob
              return $ RelativeProof res subproof
      where 
            prob'                  = prob{startTerms = TermAlgebra}
            remproc :+: subproc    = S.processorArgs inst
            (applicable, reason)   = appliesTo prob

relative :: (P.Processor sub, P.Processor relproc) => P.InstanceOf relproc -> P.InstanceOf sub -> P.InstanceOf (S.StdProcessor (RelativeProcessor relproc sub))
relative rel sub = RelativeProcessor `S.withArgs` (rel :+: sub)

relativeProcessor :: S.StdProcessor (RelativeProcessor P.AnyProcessor P.AnyProcessor)
relativeProcessor = S.StdProcessor RelativeProcessor