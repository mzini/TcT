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

{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DeriveDataTypeable #-}

module Tct.Method.ComposeRC where

import Data.Typeable (Typeable)
import Text.PrettyPrint.HughesPJ

import qualified Tct.Processor as P
import qualified Tct.Processor.Transformations as T
import Tct.Processor.Args
import qualified Tct.Processor.Args as A
import Tct.Processor.PPrint
import Tct.Processor.Args.Instances
import Tct.Processor (Answerable (..), certificate)
import qualified Tct.Certificate as Cert

import Termlib.Trs.PrettyPrint (pprintNamedTrs)
import Termlib.Utils (PrettyPrintable (..))
import Termlib.Trs (Trs(..), union, (\\))
import qualified Termlib.Trs as Trs
import qualified Termlib.Rule as Rule
import Termlib.Rule (Rule)
import Termlib.Problem (Problem (..), StartTerms (..))
import qualified Termlib.Problem as Prob
import Tct.Method.DP.DependencyGraph
import qualified Tct.Method.DP.DependencyGraph as DG
import Tct.Method.Compose hiding (progress)


data ComposeRCProc p1 p2 = ComposeRCProc

data ComposeRCProof p1 p2 = ComposeRCProof Partitioning [Rule.Rule] (Maybe (P.Proof p2)) (Maybe (P.Proof p2))
                          | ComposeRCInapplicable String


progress :: (P.Processor p1, P.Processor p2) => ComposeRCProof p1 p2 -> Bool
progress (ComposeRCProof _ _ msp1 msp2) = undefined
--    not (Trs.isEmpty $ Prob.strictComponents $ P.inputProblem sp) && P.succeeded sp
progress ComposeRCInapplicable {} = False

instance AssocArgument (RuleSelector ()) where 
    assoc _ = [] -- TODO extend


instance (P.Processor p1, P.Processor p2) => T.Transformer (ComposeRCProc p1 p2) where
    type T.ArgumentsOf (ComposeRCProc p1 p2) = Arg (Assoc (RuleSelector ())) :+: Arg (Maybe (Proc p1)) :+: Arg (Maybe (Proc p2))
    type T.ProofOf (ComposeRCProc p1 p2)     = ComposeRCProof p1 p2

    name ComposeRCProc        = "compose-rc"
    instanceName inst   = show $ text "compose-rc" <+> parens (ppsplit)
        where split :+: _ = T.transformationArgs inst
              ppsplit = text $ show split 

    description ComposeRCProc = [ unwords [ ] ]
    arguments ComposeRCProc   = opt { A.name         = "split" 
                                    , A.defaultValue = selFirstCongruences
                                    , A.description  = ""}
                                :+: opt { A.name = "subprocessor 1"
                                        , A.defaultValue = Nothing
                                        , A.description = ""}
                                :+: opt { A.name = "subprocessor 2"
                                        , A.defaultValue = Nothing
                                        , A.description = ""}

    transform inst prob = undefined
        -- case split of 
        --   Static (_,fn) -> do sp1 <- P.apply inst1 prob1
        --                       return $ mkResult sp1 (rDps, sDps) (rTrs, sTrs)                         
              where rs = rsSelect s () prob
                    s :+: mp1 :+: mp2 = T.transformationArgs inst

instance T.TransformationProof (ComposeRCProc p1 p2) where