{-# OPTIONS_HADDOCK hide #-}
--------------------------------------------------------------------------------
-- | 
-- Module      :  Tct.Method.DP.Utils
-- Copyright   :  (c) Martin Avanzini <martin.avanzini@uibk.ac.at>, 
--                Georg Moser <georg.moser@uibk.ac.at>, 
--                Andreas Schnabl <andreas.schnabl@uibk.ac.at>,
-- License     :  LGPL (see COPYING)
--
-- Maintainer  :  Martin Avanzini <martin.avanzini@uibk.ac.at>
-- Stability   :  unstable
-- Portability :  unportable      
-- 
-- This module provides standard errors for processors
-- working on dependency pair problem.
--------------------------------------------------------------------------------   

module Tct.Method.DP.Utils where

import Text.PrettyPrint.HughesPJ hiding (empty)

import Termlib.Utils
import qualified Tct.Utils.Xml as Xml

data DPError = NonDPProblemGiven 
             | NonRCProblemGiven
             | NotApplicable Doc
             | ContainsStrictRule

instance PrettyPrintable DPError where 
    pprint NonDPProblemGiven = text "The input problem is not a DP-problem."
    pprint NonRCProblemGiven = text "The input problem is not an RC-problem."
    pprint (NotApplicable r) = hang (text "The processor is not applicable. Reason:") 3 r
    pprint ContainsStrictRule = paragraph "The processor is inapplicable since the strict component of the input problem is not empty"
    

errorToXml :: DPError -> Xml.XmlContent
errorToXml err = 
           Xml.elt "dperror" [] [errXml err]
    where 
      errXml NonDPProblemGiven = Xml.elt "nodpproblem" [] []
      errXml NonRCProblemGiven = Xml.elt "norcproblem" [] []
      errXml (NotApplicable r) = Xml.elt "notapplicable" [] [ Xml.text $ show r ]
      errXml ContainsStrictRule = Xml.elt "containsstrictrule" [] []
