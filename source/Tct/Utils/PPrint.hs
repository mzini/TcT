
----------------------------------------------------------------------------------
-- |
-- Module      :  Tct.Utils.PPrint
-- Copyright   :  (c) Martin Avanzini <martin.avanzini@uibk.ac.at>, 
--                Georg Moser <georg.moser@uibk.ac.at>, 
--                Andreas Schnabl <andreas.schnabl@uibk.ac.at>
-- License     :  LGPL (see COPYING)
-- Maintainer  :  Martin Avanzini <martin.avanzini@uibk.ac.at>
-- Stability   :  unstable
-- Portability :  unportable      
--
-- This module provides utilities for pretty printing.
--
----------------------------------------------------------------------------------

module Tct.Utils.PPrint 
       (
         heading
       , indent
       , enum
       , block
       , block'
       )
       where

import Text.PrettyPrint.HughesPJ
import Termlib.Utils (PrettyPrintable (..), underline)
import Tct.Utils.Enum

-- | Pretty print string as heading.
heading :: String -> Doc
heading n = underline (text $ n ++ ":")

-- | Pretty print indented.
indent :: Doc -> Doc
indent = nest 2 

-- | Pretty Printer for enumerations.
enum :: (PrettyPrintable t) => Enumeration t -> Doc
enum es =  vcat [pprint a <> text ")" <+> pprint e $+$ text "" | (a,e) <- es]


-- | Pretty prints block with given name, and content
-- as given by enumeration.
block :: (PrettyPrintable t) => String -> Enumeration t -> Doc
block _ [] = empty
block h [(_,d)] = heading h $+$ (indent $ pprint d)
block h ds = heading h $+$ (indent $ enum ds)

-- | Like 'block', but expects a list instead of an enumeration.
block' :: (PrettyPrintable t) => String -> [t] -> Doc
block' h ds = block h (enumeration' ds)




