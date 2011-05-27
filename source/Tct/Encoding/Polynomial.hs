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

{-# LANGUAGE DeriveDataTypeable #-}

module Tct.Encoding.Polynomial where

import qualified Data.List as List
import Data.Typeable

import Qlogic.Semiring

newtype Polynomial a b = Poly [Monomial a b]
data Monomial a b = Mono b [Power a]
                    deriving (Eq, Ord, Show, Typeable)
data Power a = Pow a Int
                    deriving (Eq, Ord, Show, Typeable)

pplus :: (Eq a, Eq b, Semiring b) => Polynomial a b -> Polynomial a b -> Polynomial a b
pplus (Poly xs) (Poly ys) = shallowSimp $ Poly $ xs ++ ys

shallowSimp :: (Eq a, Eq b, Semiring b) => Polynomial a b -> Polynomial a b
shallowSimp (Poly []) = Poly []
shallowSimp (Poly (Mono n _ :ms)) | n == zero = shallowSimp $ Poly ms
shallowSimp (Poly (Mono n xs:ms)) | otherwise = Poly $ (Mono (foldl addcoeff n xss) xs):subresult
                                                where (xss, yss)            = List.partition (\(Mono _ xs') -> xs == xs') ms
                                                      addcoeff x (Mono y _) = x `plus` y
                                                      Poly subresult        = shallowSimp $ Poly yss

pprod :: Polynomial a b -> Polynomial a b -> Polynomial a b
pprod = undefined
