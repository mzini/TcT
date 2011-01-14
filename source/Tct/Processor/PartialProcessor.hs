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

module Tct.Processor.PartialProcessor where

import Text.PrettyPrint.HughesPJ

import Termlib.Problem
import Termlib.Trs (Trs)
import Termlib.Utils (PrettyPrintable(..))
import qualified Termlib.Trs as Trs

import Tct.Processor.Args
import Tct.Processor.Args.Instances()
import Tct.Proof
import qualified Tct.Processor as P
import qualified Tct.Processor.Standard as S

class P.Processor p => PartialProcessor p where
  solvePartial :: P.SolverM m => P.InstanceOf p -> Problem -> m (PartialProof p)


data SomePartialProcessor = forall p. (P.ParsableProcessor p, PartialProcessor p) => SomePartialProcessor p

-- Proof Objects

data PartialProof p = PartialProof { inputProblem :: Problem
                                   , ppProof :: P.ProofOf p
                                   , ppStrict :: Trs
                                   }

data RelativeProof p sub = RelativeProof (PartialProof p) (P.Proof sub)

instance P.Processor p => Answerable (PartialProof p) where
    answer = answer . ppProof

instance Answerable (P.ProofOf sub) => Answerable (RelativeProof p sub) where 
    answer (RelativeProof _ subp) = answer subp

instance P.Processor p => PrettyPrintable (PartialProof p) where
  pprint p = text "The following rules were strictly oriented by the relative processor:"
             $+$ pprint (ppStrict p, signature $ inputProblem p, variables $ inputProblem p)
             $+$ text ""
             $+$ pprint (ppProof p)

instance (P.Processor p, P.Processor sub) => PrettyPrintable (RelativeProof p sub) where
  pprint (RelativeProof pp subp) = case succeeded pp of
                                     True  -> text "First we apply the relative processor:"
                                             $+$ pprint pp
                                             $+$ text ""
                                             $+$ text "Next, we apply the subprocessor:"
                                             $+$ pprint subp
                                     False -> text "The relative processor was not successful. We apply the subprocessor directly"
                                             $+$ pprint subp


-- Relative Processor

data RelativeProcessor p sub = RelativeProcessor

instance (P.Processor sub, PartialProcessor p) => S.Processor (RelativeProcessor p sub) where
  name RelativeProcessor = "relative"

  type S.ArgumentsOf (RelativeProcessor p sub) = Arg (S.StdProcessor p) :+: Arg (S.StdProcessor sub)
  type S.ProofOf (RelativeProcessor p sub)     = RelativeProof p sub

  arguments RelativeProcessor = arg { name = "deleteWith"
                                     , description = unlines [ "The subprocessor that is applied after the current processor."
                                                             , "The value 'none' forces the current processor to orient all rules strictly."]}
                             :+: arg { name = "subprocessor"
                                     , description = unlines [ "The subprocessor that is applied on the remaining problem."]}

  solve inst prob = do res <- solvePartial p prob
                       let subprob = case relation prob of
                                       Standard trs         -> prob'{relation = Standard $ trs Trs.\\ ppStrict res}
                                       Relative strict weak -> prob'{relation = Relative (strict Trs.\\ ppStrict res) weak}
                                       DP       _      _    -> error "Relative Rule Removal inapplicable for DP problems"
                       subproof <- P.apply sub subprob
                       return $ RelativeProof res subproof
      where prob'     = prob{startTerms = TermAlgebra}
            p :+: sub = S.processorArgs inst

