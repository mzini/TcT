{-# LANGUAGE UndecidableInstances #-}
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
    , VerificationStatus (..)
    , Verifiable (..)
    , succeeded
    , failed
    , isTimeout
    , certificate
    , answerFromCertificate
    , andVerify
    , allVerify
    )
where

import Text.PrettyPrint.HughesPJ
import Text.ParserCombinators.Parsec hiding (parse)
import Termlib.Utils (PrettyPrintable (..), Parsable (..))
import Termlib.Problem (Problem)
import Tct.Certificate (Certificate, uncertified)

data Answer = CertAnswer Certificate 
            | MaybeAnswer
            | YesAnswer
            | NoAnswer
            | TimeoutAnswer deriving (Eq, Ord, Show)

instance Parsable Answer where
  parse = parseYes <|> parseMaybe <|> parseTimeout
    where parseMaybe   = string "MAYBE" >> return MaybeAnswer
          parseTimeout = string "TIMEOUT" >> return TimeoutAnswer
          parseYes     = parse >>= return . CertAnswer

instance PrettyPrintable Answer where 
  pprint (CertAnswer cert) = pprint cert
  pprint TimeoutAnswer     = text "TIMEOUT"
  pprint MaybeAnswer       = text "MAYBE"
  pprint YesAnswer         = text "YES"
  pprint NoAnswer          = text "NO"


class Answerable proof where 
    answer :: proof -> Answer

instance Answerable Answer where
    answer = id

answerFromCertificate :: Certificate -> Answer
answerFromCertificate cert = if cert == uncertified
                             then MaybeAnswer
                             else CertAnswer cert

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

certificate :: Answerable p => p -> Certificate
certificate p = case answer p of 
                CertAnswer c -> c
                _            -> uncertified

data VerificationStatus = NotChecked
                        | VerificationOK
                        | VerificationFail Doc

class Verifiable proof where 
    verify :: Problem -> proof -> VerificationStatus
    verify _ _ = NotChecked


andVerify :: VerificationStatus -> VerificationStatus -> VerificationStatus
s@(VerificationFail _) `andVerify` _                      = s
_                      `andVerify` t@(VerificationFail _) = t
s@NotChecked           `andVerify` _                      = s
_                      `andVerify` t@NotChecked           = t
VerificationOK         `andVerify` VerificationOK         = VerificationOK

allVerify :: [VerificationStatus] -> VerificationStatus
allVerify = foldr andVerify VerificationOK

class (Answerable proof, PrettyPrintable proof, Verifiable proof) => ComplexityProof proof
instance (Answerable proof, PrettyPrintable proof, Verifiable proof) => ComplexityProof proof


