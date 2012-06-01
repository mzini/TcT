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
      , catchException
    )
where

import qualified Control.Exception as E
import Control.Monad.Error (liftIO)

import Termlib.Utils (paragraph)  
import Text.PrettyPrint.HughesPJ
import Tct.Certificate (constant, certified)
import Tct.Processor (Answer (..), ComplexityProof(..), SolverM(..))

import Tct.Utils.PPrint (indent)
import qualified Control.Exception as C
import qualified Tct.Utils.Xml as Xml

data OrientationProof o = Order o -- ^ Proven with given order.
                        | Incompatible -- ^ The problem is incompatible.
                        | Empty  -- ^ The problem is empty
                        | Inapplicable String -- ^ Inapplicable for given reason.
                        | ExceptionRaised C.AsyncException -- ^ Some exception was raised.
  deriving Show

instance ComplexityProof o => ComplexityProof (OrientationProof o) where
    pprintProof Empty            _    = text "All strict components are empty, nothing to further orient"
    pprintProof (Order o)        mde  = pprintProof o mde
    pprintProof Incompatible     _    = text "The input cannot be shown compatible"
    pprintProof (Inapplicable s) _    = text "The processor is inapplicable, reason:"
                                        $+$ indent (text s)
    pprintProof (ExceptionRaised e) _ = text "Following exception was raised:"
                                        $+$ indent (paragraph $ show e)

    answer (Order o) = answer o
    answer Empty     = CertAnswer $ certified (constant, constant)
    answer _ = MaybeAnswer

    toXml ord = Xml.elt "order" [] [toXml' ord]
      where toXml' (Order o) = Xml.elt "compatible" [] [toXml o]
            toXml' Incompatible = Xml.elt "incompatible" [] []
            toXml' Empty = Xml.elt "empty" [] []    
            toXml' (Inapplicable r) = Xml.elt "inapplicable" [] [Xml.text r]    
            toXml' (ExceptionRaised e) = Xml.elt "exceptionRaised" [] [Xml.text $ show e]
            
            
catchException :: SolverM m => m (OrientationProof o) -> m (OrientationProof o)
catchException m = 
  do io <- mkIO m 
     liftIO $ E.catchJust notKill io (return . ExceptionRaised)
  where notKill E.ThreadKilled = Nothing
        notKill e = Just e
    