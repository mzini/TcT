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

module Tct.Proof
    ( ComplexityProof
    , Answer (..)
    , Answerable (..)
    , succeeded
    , failed
    , isTimeout
    , certificate
    )
where

import Text.PrettyPrint.HughesPJ

import Termlib.Utils (PrettyPrintable (..))
import Tct.Certificate (Certificate)

data Answer = CertAnswer Certificate 
            | FailAnswer
            | YesAnswer
            | TimeoutAnswer deriving (Eq, Ord, Show)

instance PrettyPrintable Answer where 
  pprint (CertAnswer cert) = pprint cert
  pprint TimeoutAnswer     = text "TIMEOUT"
  pprint FailAnswer        = text "MAYBE"
  pprint YesAnswer         = text "YES"


class Answerable proof where 
    answer :: proof -> Answer

instance Answerable Answer where
    answer = id


succeeded :: Answerable p => p -> Bool
succeeded p = case answer p of 
                CertAnswer _ -> True
                YesAnswer    -> True
                _            -> False

failed :: Answerable p => p -> Bool
failed = not . succeeded

isTimeout :: Answerable p => p -> Bool
isTimeout p = case answer p of 
                TimeoutAnswer -> True
                _             -> False

certificate :: Answerable p => p -> Maybe Certificate
certificate p = case answer p of 
                CertAnswer c -> Just c
                _            -> Nothing

class (Answerable proof, PrettyPrintable proof) => ComplexityProof proof




