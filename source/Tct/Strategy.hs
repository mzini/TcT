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

{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}

module Tct.Strategy where

import Text.ParserCombinators.Parsec.Char
import Text.ParserCombinators.Parsec hiding (parse)
import Text.PrettyPrint.HughesPJ hiding (parens)

import Termlib.Utils

import Tct.Processor.SomeProcessor
import Tct.Processor.Timeout (timeout)
import Tct.Strategy.Flag
import Tct.Strategy.Parse

class Show strat => Strategy strat where
  strategyName :: strat -> String
  flags :: strat -> Flags
  description :: strat -> [String]
  parseProcessor :: strat -> StrategyParser SomeProcessor
  synopsis :: strat -> Doc
  synopsis strat = defaultSynopsis strat

defaultSynopsis :: Strategy strat => strat -> Doc
defaultSynopsis strat = (text (strategyName strat) <+>  if flgs == noFlags then empty else text "<flags>")  
                        $++$ text "Here <flags> may be one of the following:" 
                        $+$  (nest 2 $ pprint flgs)
    where flgs = flags strat


type StrategyParser a = CharParser [SomeStrategy] a

parseSomeProcessor :: StrategyParser SomeProcessor
parseSomeProcessor = do strats <- getState
                        proc <- parens parseSomeProcessor <|> choice [ parseProcessor s | SomeStrategy s <- strats]
                        to <- parseTimeout
                        return $ mk to proc
    where mk (Just n) p = timeout n p
          mk Nothing p = p

data SomeStrategy = forall strat. (Strategy strat) => SomeStrategy strat

instance Show SomeStrategy where
  show (SomeStrategy s) = "SomeStrategy (" ++ show s ++ ")"

instance Strategy SomeStrategy where
  strategyName (SomeStrategy s)   = strategyName s
  flags (SomeStrategy s)          = flags s
  description (SomeStrategy s)    = description s
  parseProcessor (SomeStrategy s) = parseProcessor s

instance PrettyPrintable SomeStrategy where
  pprint (SomeStrategy strat) = ppheading $$ (nest 2 $ ppdescr $++$ ppsyn)
    where ppheading = text "Strategy" <+> doubleQuotes (text sname) <> text ":"
          ppdescr = vcat [fsep $ [text w | w <- words s] | s <- descr] 
          ppsyn = text "Usage:" $+$ text "" $+$  (nest 2 $ synopsis strat)
          sname = strategyName strat 
          descr = description strat

strategyFromString :: SourceName -> [SomeStrategy] -> String -> Either ParseError SomeProcessor
strategyFromString sn builtins = fromString parseSomeProcessor builtins sn