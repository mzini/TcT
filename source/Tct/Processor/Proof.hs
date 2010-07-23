{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE OverlappingInstances #-}
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

{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}

module Tct.Processor.Proof 
    (
     Answer (..)
    , Answerable (..)
    )
where

import Termlib.Utils
import Text.PrettyPrint.HughesPJ

import Termlib.Problem (prettyPrintRelation, measureName)
import qualified Tct.Proof as P
import Tct.Proof (succeeded, certificate)
import Tct.Processor
import Tct.Certificate (Certificate, uncertified)


instance (Processor proc, PrettyPrintable (ProofFrom proc)) => PrettyPrintable (PartialProof proc) where
    pprint pp = text "The Processor oriented the following rules strictly:"
                $+$ text ""
                $+$ pprint (ppStrict pp, ppSig pp, ppVars pp)
                $+$ text ""
                $+$ text "Details:" 
                $+$ (nest 3 $ pprint $ ppProof pp)
                $+$ text ""

instance (Processor proc, P.Proof (ProofFrom proc)) => P.Proof (PartialProof proc) where
    succeeded = succeeded . ppProof

instance Processor proc => PrettyPrintable (Proof proc) where
    pprint p@(Proof proc prob res) = ppheading $+$ text "" $+$ ppres
        where ppheading = (pphead $+$ underline) $+$ ppanswer $+$ ppinput
              pphead    = quotes (text (name 3 proc))
              ppres     = pt "Details" $+$ nest 2 (pprint res)
              ppinput   = pt "Input Problem" <+> measureName prob <+> text "with respect to"
                          $+$ nest 2 (prettyPrintRelation prob)
              ppanswer  = pt "Answer" <+> pprint (answer p) <+> ppreason 
              ppreason  = case res of 
                            Right p' | succeeded p' -> empty
                                     | otherwise    -> text "(subprocessor failed)"
                            _                       -> empty
              underline = text (take (length $ show pphead) $ repeat '-')
              pt s = wtext 17 $ s ++  ":"
              wtext i s = text $ take n $ s ++ repeat ' ' where n = max i (length s)

instance Processor proc => P.Proof (Proof proc) where succeeded = succeeded . result
instance Processor proc => P.ComplexityProof (Proof proc) where certificate = certificate . result



instance P.Proof Answer where 
    succeeded (CertAnswer _) = True
    succeeded _              = False

instance P.ComplexityProof Answer where 
    certificate (CertAnswer c) = c
    certificate _              = uncertified

instance PrettyPrintable Answer where 
  pprint (CertAnswer cert) = pprint cert
  pprint TimeoutAnswer     = text "TIMEOUT"
  pprint FailAnswer        = text "MAYBE"


data Answer = CertAnswer Certificate 
            | FailAnswer
            | TimeoutAnswer deriving (Eq, Ord, Show)

class Answerable a where 
    answer :: a -> Answer

instance P.ComplexityProof p => Answerable p where 
    answer p | succeeded p = CertAnswer $ certificate p
             | otherwise   = FailAnswer


    
instance (Answerable (ProofFrom proc)) => Answerable (Proof proc) where
    answer p = either (const FailAnswer) answer (result p)