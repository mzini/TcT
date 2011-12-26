{- | 
Module      :  Tct.Encoding.Polynomial
Copyright   :  (c) Martin Avanzini <martin.avanzini@uibk.ac.at>, 
               Georg Moser <georg.moser@uibk.ac.at>, 
               Andreas Schnabl <andreas.schnabl@uibk.ac.at>
License     :  LGPL (see COPYING)

Maintainer  :  Andreas Schnabl <andreas.schnabl@uibk.ac.at>
Stability   :  unstable
Portability :  unportable      
-}

{-# LANGUAGE DeriveDataTypeable #-}

module Tct.Encoding.Polynomial where

import qualified Data.List as List
import Data.Typeable

import Qlogic.Semiring

newtype Polynomial a b = Poly [Monomial a b]
                         deriving (Eq, Ord, Show, Typeable)
data Monomial a b = Mono b [Power a]
                    deriving (Eq, Ord, Show, Typeable)
data Power a = Pow a Int
                    deriving (Eq, Ord, Show, Typeable)

getCoeff :: (Eq a, Semiring b) => [Power a] -> Polynomial a b -> b
getCoeff _ (Poly [])                         = zero
getCoeff v (Poly (Mono n w:ms)) | powsEq v w = n `plus` getCoeff v (Poly ms)
                                | otherwise  = getCoeff v $ Poly ms

getFirstCoeff :: Eq a => [Power a] -> Polynomial a b -> Maybe b
getFirstCoeff _ (Poly []) = Nothing
getFirstCoeff v (Poly (Mono n w:ms)) | powsEq v w = Just n
                                     | otherwise  = getFirstCoeff v $ Poly ms

deleteCoeff :: Eq a => [Power a] -> Polynomial a b -> Polynomial a b
deleteCoeff _ (Poly [])                         = Poly []
deleteCoeff v (Poly (Mono n w:ms)) | powsEq v w = Poly subresult
                                   | otherwise  = Poly $ Mono n w:subresult
  where Poly subresult = deleteCoeff v $ Poly ms

deleteFirstCoeff :: Eq a => [Power a] -> Polynomial a b -> Polynomial a b
deleteFirstCoeff _ (Poly [])                         = Poly []
deleteFirstCoeff v (Poly (Mono n w:ms)) | powsEq v w = Poly ms
                                        | otherwise  = Poly $ Mono n w:subresult
  where Poly subresult = deleteFirstCoeff v $ Poly ms

splitFirstCoeff :: Eq a => [Power a] -> Polynomial a b -> (Maybe b, Polynomial a b)
splitFirstCoeff _ (Poly [])                         = (Nothing, Poly [])
splitFirstCoeff v (Poly (Mono n w:ms)) | powsEq v w = (Just n, Poly ms)
                                       | otherwise  = (subres, Poly $ Mono n w:subpoly)
  where (subres, Poly subpoly) = splitFirstCoeff v $ Poly ms

powsEq :: Eq a => [Power a] -> [Power a] -> Bool
powsEq []     [] = True
powsEq []     _  = False
powsEq (v:vs) ws | v `elem` ws = powsEq vs $ List.delete v ws
                 | otherwise   = False

pplus :: (Eq a, Eq b, Semiring b) => Polynomial a b -> Polynomial a b -> Polynomial a b
pplus (Poly xs) (Poly ys) = shallowSimp $ Poly $ xs ++ ys

bigPplus :: (Eq a, Eq b, Semiring b) => [Polynomial a b] -> Polynomial a b
bigPplus = shallowSimp . Poly . concat . map (\(Poly p) -> p)

shallowSimp :: (Eq a, Eq b, Semiring b) => Polynomial a b -> Polynomial a b
shallowSimp (Poly []) = Poly []
shallowSimp (Poly (Mono n _ :ms)) | n == zero = shallowSimp $ Poly ms
shallowSimp (Poly (Mono n xs:ms)) | otherwise = Poly $ (Mono (foldl addcoeff n xss) xs):subresult
                                                where (xss, yss)            = List.partition (\(Mono _ xs') -> xs == xs') ms
                                                      addcoeff x (Mono y _) = x `plus` y
                                                      Poly subresult        = shallowSimp $ Poly yss

unEmpty :: Semiring b => Polynomial a b -> Polynomial a b
unEmpty (Poly []) = constToPoly zero
unEmpty p         = p

pprod :: (Eq a, Eq b, Semiring b) => Polynomial a b -> Polynomial a b -> Polynomial a b
pprod (Poly xs) p = bigPplus $ map (\x -> pmprod x p) xs

bigPprod :: (Eq a, Eq b, Semiring b) => [Polynomial a b] -> Polynomial a b
bigPprod = foldr pprod $ constToPoly one

pmprod :: (Eq a, Semiring b) => Monomial a b -> Polynomial a b -> Polynomial a b
pmprod m (Poly ns) = Poly $ map (\n -> mprod m n) ns

mprod :: (Eq a, Semiring b) => Monomial a b -> Monomial a b -> Monomial a b
mprod (Mono m xs) (Mono n ys) = simpMono $ Mono (m `prod` n) (xs ++ ys)

cpprod :: Semiring b => b -> Polynomial a b -> Polynomial a b
cpprod n (Poly xs) = Poly $ map (cmprod n) xs

cmprod :: Semiring b => b -> Monomial a b -> Monomial a b
cmprod n (Mono m vs) = Mono (n `prod` m) vs

simpMono :: Eq a => Monomial a b -> Monomial a b
simpMono (Mono n xs) = Mono n $ simpPower xs

simpPower :: Eq a => [Power a] -> [Power a]
simpPower [] = []
simpPower ((Pow _ n):xs) | n == 0    = simpPower xs
simpPower ((Pow v n):xs) | otherwise = (Pow v (foldl addpow n xss):(simpPower yss))
                                       where (xss, yss)           = List.partition isRightPow xs
                                             isRightPow (Pow w _) = v == w
                                             addpow x (Pow _ y)   = x + y

varToPoly :: Semiring b => a -> Polynomial a b
varToPoly v = Poly [Mono one [Pow v 1]]

constToPoly :: b -> Polynomial a b
constToPoly n = Poly [Mono n []]
