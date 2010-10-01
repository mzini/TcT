{-# LANGUAGE FlexibleContexts #-}
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

module Tct.Processor.PPrint where

import Text.PrettyPrint.HughesPJ
import Termlib.Utils (PrettyPrintable (..), underline, enumerated, pprintInt)
import Termlib.Problem (prettyPrintRelation)
import Tct.Proof
import qualified Tct.Processor as P

heading :: String -> Doc
heading n = underline (text $ n ++ ":")

enum :: (PrettyPrintable t) => [t] -> Doc
enum ps = enumerated [pprintInt i | i <- [1..]] [pprint p $+$ text "" | p <- ps]


block :: (PrettyPrintable t) => String -> [t] -> Doc
block _ [] = empty
block h [d] = heading h $+$ (nest 2 $ pprint d)
block h ds = heading h $+$ (nest 2 $ enum ds)

procName :: (P.Processor a) => P.Proof a -> Doc
procName p = quotes $ text $ P.instanceName $ P.appliedProcessor p


details :: (P.Processor a, Answerable (P.ProofOf a), PrettyPrintable (P.ProofOf a)) => [P.Proof a] -> Doc
details ps | any failed ps = detailsFailed ps
           | otherwise     = detailsSuccess ps

detailsFailed :: (P.Processor a, Answerable (P.ProofOf a), PrettyPrintable (P.ProofOf a)) => [P.Proof a] -> Doc
detailsFailed ps = block "Details (of failed attempts)" [procName p $+$ (nest 1 $ pprint $ P.result p) | p <- ps, failed p]

detailsSuccess :: (P.Processor a, PrettyPrintable (P.ProofOf a)) => [P.Proof a] -> Doc
detailsSuccess ps = block "Details" [procName p $+$ (nest 1 $ pprint $ P.result p) | p <- ps]

overview :: (P.Processor a, Answerable (P.ProofOf a)) => [P.Proof a] -> Doc
overview ps = block "Overview" [ppOverview p | p <- ps]
    where ppOverview p = procName p <+> status <+> text "on the subproblem defined by:"
                         $+$ nest 2 (prettyPrintRelation (P.inputProblem p))
                           where status | succeeded p = text "reports bound" <+> pprint (answer p)
                                        | otherwise   = text "FAILED"
