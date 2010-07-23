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
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ExistentialQuantification #-}
module Tct.Processor.SomeProcessor 
 (SomeProcessor (..))
where

import Control.Monad (liftM)
import Data.Typeable 

import Termlib.Utils (PrettyPrintable (..))

import Tct.Processor
import Tct.Proof (succeeded, certificate)
import qualified Tct.Proof as P


data SomeProcessor = forall proc. (Processor proc) => SomeProcessor proc deriving Typeable

data instance (ProofFrom SomeProcessor) = forall p. (P.ComplexityProof p) => SomeProof p
instance PrettyPrintable (ProofFrom SomeProcessor)   where pprint (SomeProof p) = pprint p
instance P.Proof (ProofFrom SomeProcessor)           where succeeded (SomeProof p) = succeeded p
instance P.ComplexityProof (ProofFrom SomeProcessor) where certificate (SomeProof p) = certificate p

instance Processor SomeProcessor where
  name i (SomeProcessor proc)           = name i proc
  solve (SomeProcessor proc) prob        = SomeProof `liftM` solve proc prob
  solvePartial (SomeProcessor proc) prob = do pp <- solvePartial proc prob
                                              return $ PartialProof { ppProof  = SomeProof $ ppProof pp
                                                                    , ppStrict = ppStrict pp
                                                                    , ppVars   = ppVars pp
                                                                    , ppSig    = ppSig pp
                                                                    , ppProc   = (SomeProcessor proc)}
