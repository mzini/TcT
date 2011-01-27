{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE ScopedTypeVariables #-}
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
import Text.Parsec.Prim
import Text.Parsec.Char

import Termlib.Problem
import Termlib.Trs (Trs)
import Termlib.Utils (PrettyPrintable(..))
import qualified Termlib.Trs as Trs
import Tct.Proof
import qualified Tct.Processor as P
import qualified Tct.Processor.Standard as S
import Tct.Processor.Args
import Tct.Processor.Args.Instances()
import Tct.Processor.Parse

class P.Processor p => PartialProcessor p where
  solvePartial :: P.SolverM m => P.InstanceOf p -> Problem -> m (PartialProof p)


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

instance (P.Processor sub, PartialProcessor p) => P.Processor (RelativeProcessor p sub) where
  name RelativeProcessor = "relative"
  instanceName _         = "relative"
  type P.ProofOf (RelativeProcessor p sub)    = RelativeProof p sub
  data P.InstanceOf (RelativeProcessor p sub) = RelativeInstance { remProc :: P.InstanceOf p
                                                                 , subProc :: P.InstanceOf sub }

  solve_ inst prob = do res <- solvePartial (remProc inst) prob
                        let subprob = case relation prob of
                                        Standard trs         -> prob'{relation = Standard $ trs Trs.\\ ppStrict res}
                                        Relative strict weak -> prob'{relation = Relative (strict Trs.\\ ppStrict res) weak}
                                        DP       _      _    -> error "Relative Rule Removal inapplicable for DP problems"
                        subproof <- P.apply (subProc inst) subprob
                        return $ RelativeProof res subproof
      where prob'     = prob{startTerms = TermAlgebra}


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
--     parseProcessor_ _ = do try (string "relative")
--                            rel <- undefined --P.parseAnyProcessor
--                            whiteSpace 
--                            sub <- P.parseAnyProcessor
--                            return $ RelativeInstance { remProc = rel, subProc = sub }

-- somepartialprocessor

-- data SomePartialProcessor = forall p. (P.ParsableProcessor p, PartialProcessor p) => SomePartialProcessor p
-- data SomePartialProcInstance  = forall p. (PartialProcessor p) => PPI (P.InstanceOf p)
-- -- instance Typeable (P.InstanceOf SomePartialProcessor) where 
-- --     typeOf (SPPI _) = mkTyConApp (mkTyCon "Tct.Processor.SPPI") [mkTyConApp (mkTyCon "SomeInstance") []]

-- instance P.Processor SomePartialProcessor where
--     type P.ProofOf    SomePartialProcessor = P.SomeProof
--     data P.InstanceOf SomePartialProcessor = SPPI SomePartialProcInstance
--     name (SomePartialProcessor proc)         = P.name proc
--     instanceName (SPPI (PPI inst))   = P.instanceName inst
--     solve_ (SPPI (PPI inst)) prob    = P.SomeProof `liftM` P.solve_ inst prob

-- instance P.ParsableProcessor SomePartialProcessor where
--     description     (SomePartialProcessor proc) = P.description proc
--     synString       (SomePartialProcessor proc) = P.synString proc
--     posArgs         (SomePartialProcessor proc) = P.posArgs proc
--     optArgs         (SomePartialProcessor proc) = P.optArgs proc
--     parseProcessor_ (SomePartialProcessor proc) = (SPPI . PPI) `liftM` P.parseProcessor_ proc

-- instance PartialProcessor SomePartialProcessor where
--     solvePartial (SPPI (PPI inst)) prob = 
--         do res <- solvePartial inst prob 
--            return $ res {ppProof = P.SomeProof $ ppProof res}
