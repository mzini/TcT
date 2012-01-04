{-# OPTIONS_HADDOCK hide #-}
----------------------------------------------------------------------------------
-- |
-- Module      :  Tct.Processor.Orderings
-- Copyright   :  (c) Martin Avanzini <martin.avanzini@uibk.ac.at>, 
--                Georg Moser <georg.moser@uibk.ac.at>, 
--                Andreas Schnabl <andreas.schnabl@uibk.ac.at>
-- License     :  LGPL (see COPYING)
-- Maintainer  :  Martin Avanzini <martin.avanzini@uibk.ac.at>
-- Stability   :  unstable
-- Portability :  unportable      
--
-- Defines the proof object for orderings.
----------------------------------------------------------------------------------

module Tct.Processor.Orderings 
    (
      OrientationProof (..)
    )
where

import Text.PrettyPrint.HughesPJ
import Tct.Certificate (constant, certified)
import Tct.Processor (Answer (..), ComplexityProof(..))
import Tct.Utils.PPrint (indent)

data OrientationProof o = Order o -- ^ Proven with given order.
                        | Incompatible -- ^ The problem is incompatible.
                        | Empty  -- ^ The problem is empty
                        | Inapplicable String -- ^ Inapplicable for given reason.
  deriving Show

instance ComplexityProof o => ComplexityProof (OrientationProof o) where
    pprintProof Empty            _  = text "All strict components are empty, nothing to further orient"
    pprintProof (Order o)        mde = pprintProof o mde
    pprintProof Incompatible     _   = text "The input cannot be shown compatible"
    pprintProof (Inapplicable s) _   = text "The processor is inapplicable, reason:"
                                       $+$ indent (text s)

    answer (Order o) = answer o
    answer Empty     = CertAnswer $ certified (constant, constant)
    answer Incompatible = MaybeAnswer
    answer (Inapplicable _) = MaybeAnswer
