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

import Termlib.Problem
import Termlib.Utils (PrettyPrintable(..))
import qualified Termlib.Trs as Trs
import Tct.Proof
import qualified Tct.Processor.Standard as S
import qualified Tct.Processor as P
import Tct.Processor.Args hiding (name, description, synopsis)
import qualified Tct.Processor.Args as A
import Tct.Processor.Args.Instances()

-- Proof Objects

data RelativeProof p sub = RelativeProof (P.PartialProof (P.ProofOf p)) (P.Proof sub)


instance Answerable (P.ProofOf sub) => Answerable (RelativeProof p sub) where 
    answer (RelativeProof _ subp) = answer subp


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

instance (P.Processor sub, P.Processor p) => S.Processor (RelativeProcessor p sub) where
  name RelativeProcessor = "relative"
  description _ = ["TODO"] 
  type S.ProofOf (RelativeProcessor p sub) = RelativeProof p sub
  type S.ArgumentsOf (RelativeProcessor p sub) = Arg (S.StdProcessor p) :+: Arg (S.StdProcessor sub)
  arguments _ = arg { A.name = "relativeprocessor"
                    , A.description = "The processor that is used to \"remove\" rules" }
                :+: arg { A.name = "subprocessor"
                        , A.description = "The processor that is applied after removing rules"}

  solve inst prob = do res <- P.solvePartial remproc prob
                       let removed = Trs.fromRules (P.ppRemovable res)
                           subprob = case relation prob of
                                       Standard trs         -> prob'{relation = Standard $ trs Trs.\\ removed}
                                       Relative strict weak -> prob'{relation = Relative (strict Trs.\\ removed) weak}
                                       DP       _      _    -> error "Relative Rule Removal inapplicable for DP problems"
                       subproof <- P.apply subproc subprob
                       return $ RelativeProof res subproof
      where prob'     = prob{startTerms = TermAlgebra}
            remproc :+: subproc = S.processorArgs inst

-- instance P.ParsableProcessor (RelativeProcessor (P.AnyProcessor P.SomeProcessor) (P.AnyProcessor P.SomeProcessor)) where
--     description _ = []
--     synString   _ = [ P.Token "relative", P.PosArg 1, P.PosArg 2]
--     optArgs     _ = []
--     posArgs     _ = [ (1, P.ArgDescr { P.adIsOptional = False
--                                      , P.adName       = "relative-processor"
--                                      , P.adDefault    = Nothing
--                                      , P.adDescr      = "The processor to remove rules with."
--                                      , P.adSynopsis   = domainName (Phantom :: Phantom (S.StdProcessor (P.AnyProcessor P.SomeProcessor)))})
--                     , (2, P.ArgDescr { P.adIsOptional = False
--                                     , P.adName       = "subprocessor"
--                                     , P.adDefault    = Nothing
--                                     , P.adDescr      = "The processor to apply after rules have been removed."
--                                     , P.adSynopsis   = domainName (Phantom :: Phantom (S.StdProcessor (P.AnyProcessor P.SomeProcessor)))})]
--     parseProcessor_ _ = do _ <- try (string "relative")
--                            rel <- P.parseAnyProcessor
--                            whiteSpace 
--                            sub <- P.parseAnyProcessor
--                            return $ RelativeInstance { remProc = rel, subProc = sub }


relative :: (P.Processor sub, P.Processor relproc) => P.InstanceOf relproc -> P.InstanceOf sub -> P.InstanceOf (S.StdProcessor (RelativeProcessor relproc sub))
relative rel sub = RelativeProcessor `S.withArgs` (rel :+: sub)

relativeProcessor :: S.StdProcessor (RelativeProcessor (P.AnyProcessor P.SomeProcessor) (P.AnyProcessor P.SomeProcessor))
relativeProcessor = S.StdProcessor RelativeProcessor