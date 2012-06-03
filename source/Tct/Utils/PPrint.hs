
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
       , Align (..)
       , columns
       )
       where

import Text.PrettyPrint.HughesPJ
import Termlib.Utils (PrettyPrintable (..), underline)
import Tct.Utils.Enum
import Data.List (transpose)

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
block h ds = heading h $+$ enum ds

-- | Like 'block', but expects a list instead of an enumeration.
block' :: (PrettyPrintable t) => String -> [t] -> Doc
block' h ds = block h (enumeration' ds)

data Align = AlignLeft | AlignRight | AlignCenter deriving (Show, Eq)

columns :: [(Align, [Doc])] -> Doc
columns cols = vcat [ pprow row | row <- rows]
    where rows      = transpose [ [ (al,len,c) | c <- cs ] | (al,len,cs) <- cols']
          -- rows'     = [ [(al, h, c) | (al,c) <- r ] 
          --             | r <- rows
          --             , let h = maximum $ 0 : [length c | (_, c) <- r]]
          cols'     = [ (al,len,cs') 
                      | (al,cs) <- cols 
                      , let cs' = [ lines $ show c | c <- cs ++ take (numrows - length cs) (repeat empty)]
                            len = maximum $ concat [ map length c | c <- cs']]
          numrows = maximum $ 0 : [length cs | (_,cs) <- cols ] 
          pprow row = vcat [ hcat [ text $ pad al len c | (al, len, c) <- rl]  
                           | rl <- transpose [ [(al, len, s) | s <- ls ++ take (height - length ls) (repeat "")] | (al, len, ls) <- row]]
            where height = maximum $ 0 : [length ls | (_, _, ls) <- row]
                  pad AlignLeft len s = s ++ ws (len - length s)
                  pad AlignRight len s = ws (len - length s) ++ s
                  pad AlignCenter len s = ws l ++ s ++ ws r 
                    where diff = len - length s
                          l = floor $ fromIntegral diff / (2.0 :: Double)
                          r = diff - l
                  ws n = take n (repeat ' ')
              -- where rowLines  = [[ pad len l | l <- ls ++ take (h - length ls) (repeat "")]  | (len,ls) <- cs]
              --       cs = [ (len, lines (show e)) | (len,e) <- row ]
              --       h  = maximum $ 1 : [length ls | (_,ls) <- cs]
              --       pad len s = s ++ take (len - length s) (repeat ' ')
          -- 
          -- cols'   = [ (i, cs ++ take (numrows - length cs) (repeat empty)) | (i,cs) <- cols]




