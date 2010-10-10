{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE ExistentialQuantification #-}
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
import Termlib.Utils (PrettyPrintable (..), underline, pprintInt)
import Termlib.Problem (prettyPrintRelation)
import Tct.Proof
import qualified Tct.Processor as P
import Data.Typeable 

heading :: String -> Doc
heading n = underline (text $ n ++ ":")

enum :: (PrettyPrintable t) => Enumeration t -> Doc
enum es =  vcat [pprint a <> text ")" <+> pprint e $+$ text "" | (a,e) <- es]

indent :: Doc -> Doc
indent = nest 2 

procName :: (P.Processor a) => P.Proof a -> Doc
procName p = quotes $ text $ P.instanceName $ P.appliedProcessor p

block :: (PrettyPrintable t) => String -> Enumeration t -> Doc
block _ [] = empty
block h [(_,d)] = heading h $+$ (indent $ pprint d)
block h ds = heading h $+$ (indent $ enum ds)

block' :: (PrettyPrintable t) => String -> [t] -> Doc
block' h ds = block h (enumeration' ds)


class (Typeable a, Eq a) => Numbering a where
    ppNumbering :: a -> Doc

instance Numbering Int where
    ppNumbering = pprintInt

instance Numbering Char where
    ppNumbering c = text [c]

instance Numbering a => Numbering [a] where
    ppNumbering as = hcat $ punctuate (text ".") [ppNumbering a | a <- as]

data SomeNumbering = forall a. Numbering a => SN a

--instance Numbering SomeNumbering where ppNumbering (SN e) = ppNumbering e
instance PrettyPrintable SomeNumbering where pprint (SN e) = ppNumbering e

type Enumeration e = [(SomeNumbering, e)]

enumeration :: Numbering a => [(a,e)] -> Enumeration e
enumeration l = [(SN a, e) | (a,e) <- l]

enumeration' :: [e] -> Enumeration e
enumeration' es = enumeration [(i,e) | (i,e) <- zip [1 :: Int ..] es]


find :: SomeNumbering -> [(SomeNumbering, a)] -> Maybe a
find (SN _) [] = Nothing
find (SN a) ((SN a', e) : es) = 
    case cast a' of 
      Just a'' -> if a == a'' then Just e else find (SN a) es
      Nothing  -> find (SN a) es

details :: (P.ComplexityProcessor a) => Enumeration (P.Proof a) -> Doc
details ps | any (failed . snd) ps = detailsFailed ps 
           | otherwise             = detailsSuccess ps

detailsFailed :: (P.ComplexityProcessor a) => Enumeration (P.Proof a) -> Doc
detailsFailed ps = block "Details of failed attempt(s)" 
                       $ [ (a, procName p <+> text "failed due to the following reason:" 
                                 $+$ (indent $ pprint $ P.result p)) 
                           | (a,p) <- ps, failed p]

detailsSuccess :: (P.ComplexityProcessor a) => Enumeration (P.Proof a) -> Doc
detailsSuccess ps = block "Details" 
                    $ [(e, procName p <+> text "succeeded with the following output:" $+$ (nest 1 $ pprint p)) 
                       | (e, p) <- ps]

overview :: (P.ComplexityProcessor a) => Enumeration (P.Proof a) -> Doc
overview ps = block "Overview" $ [(e, ppOverview p) | (e,p) <- ps]
    where ppOverview p = procName p <+> status <+> text "on the subproblem defined by:"
                         $+$ indent (prettyPrintRelation (P.inputProblem p))
                           where status | succeeded p = text "reports bound" <+> pprint (answer p)
                                        | otherwise   = text "FAILED"


