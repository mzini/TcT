{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleContexts #-}

----------------------------------------------------------------------------------
-- |
-- Module      :  Tct.Utils.Enum
-- Copyright   :  (c) Martin Avanzini <martin.avanzini@uibk.ac.at>, 
--                Georg Moser <georg.moser@uibk.ac.at>, 
--                Andreas Schnabl <andreas.schnabl@uibk.ac.at>
-- License     :  LGPL (see COPYING)
-- Maintainer  :  Martin Avanzini <martin.avanzini@uibk.ac.at>
-- Stability   :  unstable
-- Portability :  unportable      
--
-- This module provides the datatype 'Enumeration' together with operations.
----------------------------------------------------------------------------------
module Tct.Utils.Enum 
       (
         Numbering (..)
       , SomeNumbering (..)
       , Enumeration
         -- * Operations
       , enumeration
       , enumeration'
       , toList
       , find
       , zipEnum
       , zipSafe
       , zipUnsafe
       , mapEnum
       , evalEnum
       )
       where

import Data.Typeable 
import Termlib.Utils (PrettyPrintable(..), pprintInt)
import Text.PrettyPrint.HughesPJ
import Control.Monad (liftM)
import Data.Maybe (catMaybes)
import Tct.Processor as P
--------------------------------------------------------------------------------
--- Numberings

-- | A numbering can be used as index in an 'Enumeration'.
class (Typeable a, Eq a) => Numbering a where
    ppNumbering :: a -> Doc

instance Numbering Int where
    ppNumbering = pprintInt

instance Numbering Char where
    ppNumbering c = text [c]

instance Numbering a => Numbering [a] where
    ppNumbering as = hcat $ punctuate (text ".") [ppNumbering a | a <- as]

instance (Numbering a, Numbering b) => Numbering (a,b) where
    ppNumbering (a,b)  = ppNumbering a <> text "." <> ppNumbering b

instance (Numbering a, Numbering b) => Numbering (Either a b) where
    ppNumbering (Left a)  = ppNumbering a
    ppNumbering (Right b) = ppNumbering b

-- | Existential quantification of 'Numbering'.
data SomeNumbering = forall a. Numbering a => SN a
instance PrettyPrintable SomeNumbering where pprint (SN e) = ppNumbering e

--------------------------------------------------------------------------------
--- Enumerations

-- | An enum is an associated list with existentially quantified
-- numberings.
type Enumeration e = [(SomeNumbering, e)]

mapEnum :: (e -> f) -> Enumeration e -> Enumeration f
f `mapEnum` l = [(n,f e) | (n,e) <- l]


enumeration :: Numbering a => [(a,e)] -> Enumeration e
enumeration l = [(SN a, e) | (a,e) <- l]

enumeration' :: [e] -> Enumeration e
enumeration' es = enumeration [(i,e) | (i,e) <- zip [1 :: Int ..] es]

toList :: Enumeration e -> [e]
toList es = map snd es

find :: Numbering n => n -> Enumeration a -> Maybe a
find _ []  = Nothing
find a  as = findBy ((==) a) as

zipEnum :: [(SomeNumbering, t)] -> [(SomeNumbering, a1)] -> [Maybe (SomeNumbering, (t, a1))]
zipEnum as bs = [ mk a (SN e1) `liftM` find e1 bs | (SN e1,a) <- as ]
  where mk a e b = (e,(a,b))
        
zipSafe :: Enumeration a -> Enumeration b -> Maybe (Enumeration (a,b))
zipSafe as bs = sequence $ zipEnum as bs

zipUnsafe :: Enumeration a -> Enumeration b -> Enumeration (a,b)
zipUnsafe as bs = catMaybes $ zipEnum as bs 


findBy :: Numbering n => (n -> Bool) -> Enumeration a -> Maybe a
findBy _ [] = Nothing
findBy p ((SN a, e) : es) = 
    case cast a of 
      Just a' | p a'      -> Just e
              | otherwise -> findBy p es
      Nothing             -> Nothing

evalEnum :: (SolverM m) => Bool -> (Enumeration (m a)) -> m (Maybe (Enumeration a))
evalEnum b ms = do rs <- evalList' b [ (,) e `liftM` m  | (e,m) <- ms ]
                   return $ sequence [ mk e (find e rs)  | (SN e,_) <- ms]
  where mk _ Nothing  = Nothing
        mk e (Just x) = Just (SN e,x)
