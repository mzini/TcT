{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeFamilies #-}

----------------------------------------------------------------------------------
-- |
-- Module      :  Tct.Proof
-- Copyright   :  (c) Martin Avanzini <martin.avanzini@uibk.ac.at>, 
--                Georg Moser <georg.moser@uibk.ac.at>, 
--                Andreas Schnabl <andreas.schnabl@uibk.ac.at>
-- License     :  LGPL (see COPYING)
-- Maintainer  :  Martin Avanzini <martin.avanzini@uibk.ac.at>
-- Stability   :  unstable
-- Portability :  unportable      
--
-- This module defines proof objects.
----------------------------------------------------------------------------------

module Tct.Proof where

import Text.PrettyPrint.HughesPJ hiding (parens)
import qualified Text.ParserCombinators.Parsec as Parsec
import qualified Text.XML.HaXml.Types as Xml

import Tct.Certificate

import Termlib.Utils (PrettyPrintable (..))
import qualified Termlib.Utils as Utils


-- | The datatype 'Answer' reflects the answer type 
-- from the complexity competition. 
data Answer = CertAnswer Certificate 
            | MaybeAnswer
            | NoAnswer
            | TimeoutAnswer deriving (Eq, Ord, Show)

-- | Abbreviation for 'CertAnswer $ certified (unknown, unknown)'.
yesAnswer :: Answer
yesAnswer = CertAnswer $ certified (unknown, unknown)


instance Utils.Parsable Answer where
  parse = parseYes Parsec.<|> parseMaybe Parsec.<|> parseNo Parsec.<|> parseTO
    where parseMaybe   = Parsec.string "MAYBE" >> return MaybeAnswer
          parseTO      = Parsec.string "TIMEOUT" >> return TimeoutAnswer
          parseNo      = Parsec.string "NO" >> return NoAnswer
          parseYes     = Utils.parse >>= return . CertAnswer

instance PrettyPrintable Answer where 
  pprint (CertAnswer cert) = pprint cert
  pprint TimeoutAnswer     = text "TIMEOUT"
  pprint MaybeAnswer       = text "MAYBE"
  pprint NoAnswer          = text "NO"

instance ComplexityProof Answer where
    pprintProof a _ = pprint a
    answer = id

-- | returns the 'Certificate' associated 
-- with the proof. 
certificate :: ComplexityProof p => p -> Certificate
certificate p = case answer p of 
                CertAnswer c -> c
                _            -> uncertified
                
-- | The predicate @'succeeded' p@ holds iff
-- @'answer' p@ is of shape @CertAnswer _@.
succeeded :: ComplexityProof p => p -> Bool
succeeded p = case answer p of 
                CertAnswer _ -> True
                _            -> False

-- | Negation of 'succeeded'.
failed :: ComplexityProof p => p -> Bool
failed = not . succeeded

-- | The predicate @'isTimeout' p@ holds iff 
-- @'answer' p@ is of shape @TimeoutAnswer _@.
isTimeout :: ComplexityProof p => p -> Bool
isTimeout p = case answer p of 
                TimeoutAnswer -> True
                _             -> False


data PPMode = ProofOutput    -- ^ standard proof output
            | StrategyOutput -- ^ also output of extended /strategy information/
            | OverviewOutput  -- ^ Only present an overview
            deriving (Show, Eq, Ord)

type XmlContent = Xml.Content ()

-- | Complexity proofs should be instance of the 'ComplexityProof' class.
class ComplexityProof proof where
    -- | Construct an 'Answer' from the proof.
    answer :: proof -> Answer
    -- | Pretty printer of proof. 
    pprintProof :: proof -> PPMode -> Doc
    
    toXml :: proof -> XmlContent
    toXml p = Xml.CElem (Xml.Elem (Xml.N "proofdata") [] [d]) ()
      where d = Xml.CString True s ()
            s = show $ pprintProof p ProofOutput 
