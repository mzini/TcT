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

{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeSynonymInstances #-}

module Encoding.Matrix where

import Prelude hiding ((&&),(||),not)
import qualified Data.Foldable as F
import Qlogic.Semiring

newtype Vector a = Vector [a] deriving Show
newtype Matrix a = Matrix [Vector a] deriving Show

instance Functor Vector where
  fmap f (Vector v) = Vector $ map f v

instance Functor Matrix where
  fmap f (Matrix m) = Matrix $ map (fmap f) m

liftVector :: ([a] -> b) -> Vector a -> b
liftVector f (Vector v) = f v

liftVector_ :: ([a] -> [b]) -> Vector a -> Vector b
liftVector_ f (Vector v) = Vector $ f v

liftMatrix :: ([Vector a] -> b) -> Matrix a -> b
liftMatrix f (Matrix m) = f m

liftMatrix_ :: ([Vector a] -> [Vector b]) -> Matrix a -> Matrix b
liftMatrix_ f (Matrix v) = Matrix $ f v

adjustv :: (a -> a) -> Int -> Vector a -> Vector a
adjustv f i (Vector v) = Vector $ fst splitv ++ (f . head . snd) splitv : (tail . snd) splitv
                         where splitv = splitAt (pred i) v

adjustm :: (a -> a) -> Int -> Int -> Matrix a -> Matrix a
adjustm f i j (Matrix m) = Matrix $ fst splitm ++ (adjustv f j . head . snd) splitm : (tail . snd) splitm
                           where splitm = splitAt (pred i) m

vecdim :: Vector a -> Int
vecdim = liftVector length

mdim :: Matrix a -> (Int, Int)
mdim (Matrix m) = if x == 0 then (0, 0) else (x, vecdim (head m))
                  where x = length m

vEntry :: Int -> Vector a -> a
vEntry i = liftVector (!! (pred i))

entry :: Int -> Int -> Matrix a -> a
entry i j = vEntry j . liftMatrix (!! (pred i))

row :: Int -> Matrix a -> Vector a
row i = liftMatrix (!! (pred i))

col :: Int -> Matrix a -> Vector a
col j m = Vector $ liftMatrix (map $ vEntry j) m

transpose :: Matrix a -> Matrix a
transpose (Matrix [])                   = Matrix []
transpose (Matrix (Vector [] : vs))     = transpose $ Matrix vs
transpose m@(Matrix (Vector (_:_) : _)) = Matrix $ headcol : tailcols
                                          where headcol         = Vector $ liftMatrix (map $ liftVector head) m
                                                Matrix tailcols = transpose $ liftMatrix_ (map $ liftVector_ tail) m

mplus :: Semiring a => Matrix a -> Matrix a -> Matrix a
mplus (Matrix vs) (Matrix ws) = Matrix $ zipWith vplus vs ws

bigmplus :: Semiring a => [Matrix a] -> Matrix a
bigmplus ms = foldr mplus (uncurry zeromatrix dim) ms
              where dim = case ms of
                            []  -> (0, 0)
                            m:_ -> mdim m

vplus :: Semiring a => Vector a -> Vector a -> Vector a
vplus (Vector v) (Vector w) = Vector $ zipWith plus v w

bigvplus :: Semiring a => [Vector a] -> Vector a
bigvplus vs = foldr vplus (zerovec dim) vs
              where dim = case vs of
                            []  -> 0
                            v:_ -> vecdim v

mprod :: Semiring a => Matrix a -> Matrix a -> Matrix a
mprod m n = transpose $ liftMatrix_ (map $ mvprod m) (transpose n)

mvprod :: Semiring a => Matrix a -> Vector a -> Vector a
mvprod m v = Vector $ liftMatrix (map (`scalarprod` v)) m

scalarprod :: Semiring a => Vector a -> Vector a -> a
scalarprod (Vector v) (Vector w) = bigPlus $ zipWith prod v w

bigmprod :: Semiring a => [Matrix a] -> Matrix a
bigmprod ms = foldr mprod (uncurry zeromatrix dim) ms
              where dim = case ms of
                            []  -> (0, 0)
                            m:_ -> mdim m

zerovec :: Semiring a => Int -> Vector a
zerovec i = Vector $ replicate i zero

zeromatrix :: Semiring a => Int -> Int -> Matrix a
zeromatrix m n = Matrix $ replicate m (Vector $ replicate n zero)

unit :: Semiring a => Int -> Matrix a
unit d | d == 0    = Matrix []
       | otherwise = Matrix $ (Vector (one : z)) : map f m
                     where Vector z     = zerovec $ pred d
                           Matrix m     = unit $ pred d
                           f (Vector v) = Vector (zero : v)

diag :: Semiring a => Matrix a -> Vector a
diag m = Vector $ map (\ i -> entry i i m) [1..l]
         where (x, y) = mdim m
               l      = min x y

diagonalNonZeroes :: AbstrOrdSemiring a Bool => Matrix a -> Int
diagonalNonZeroes m = length $ filter (./=. zero) dia
                      where (Vector dia) = diag m

diagonalZeroes :: AbstrOrdSemiring a Bool => Matrix a -> Int
diagonalZeroes m = length $ filter (.==. zero) dia
                   where (Vector dia) = diag m

maximumMatrix :: (F.Foldable t, AbstrOrdSemiring a Bool) => t (Matrix a) -> Matrix a
maximumMatrix ms = F.foldr maxMatrix (uncurry zeromatrix dim) ms
                   where dim = case F.toList ms of
                                 []  -> (0, 0)
                                 m:_ -> mdim m

maxMatrix :: AbstrOrdSemiring a Bool => Matrix a -> Matrix a -> Matrix a
maxMatrix (Matrix m) (Matrix n) = Matrix $ zipWith maxVector m n

maximumVector :: (F.Foldable t, AbstrOrdSemiring a Bool) => t (Vector a) -> Vector a
maximumVector vs = F.foldr maxVector (zerovec dim) vs
                   where dim = case F.toList vs of
                                 []  -> 0
                                 v:_ -> vecdim v

maxVector :: AbstrOrdSemiring a Bool => Vector a -> Vector a -> Vector a
maxVector (Vector v) (Vector w) = Vector $ zipWith amax v w
                                  where amax a b = if a .>=. b then a else b

type MatrixCompare a b = Matrix a -> Matrix a -> b
type VectorCompare a b = Vector a -> Vector a -> b

-- vGrt :: AbstrOrd a b => VectorCompare a b
-- vGrt = (.>.)

-- vChkGrt :: Ord a => VectorCheck a
-- vChkGrt [] _          = False
-- vChkGrt _ []          = False
-- vChkGrt (v:vs) (w:ws) = (v > w) && (vChkGeq vs ws)

-- vGeq :: AbstrOrd a b => VectorCompare a b
-- vGeq = (.>=.)

-- vChkGeq :: Ord a => VectorCheck a
-- vChkGeq vs ws = and (zipWith (>=) vs ws)

-- vEqu :: AbstrEq a b => VectorCompare a b
-- vEqu = (.==.)

-- vChkEqu :: Eq a => VectorCheck a
-- vChkEqu vs ws = and (zipWith (==) vs ws)

-- mGeq :: AbstrOrd a b => MatrixCompare a b
-- mGeq = (.>=.)

-- mChkGeq :: Ord a => MatrixCheck a
-- mChkGeq vs = and . zipWith vChkGeq vs
