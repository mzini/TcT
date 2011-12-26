{- | 
Module      :  Tct.Encoding.Relative
Copyright   :  (c) Martin Avanzini <martin.avanzini@uibk.ac.at>, 
               Georg Moser <georg.moser@uibk.ac.at>, 
               Andreas Schnabl <andreas.schnabl@uibk.ac.at>
License     :  LGPL (see COPYING)

Maintainer  :  Martin Avanzini <martin.avanzini@uibk.ac.at>
Stability   :  unstable
Portability :  unportable      

This module implements a SAT encoding for relative rewriting, 
where not all rules are strictly oriented.
-}

{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Tct.Encoding.Relative 
    ( 
    Orientation
    , strictlyOriented
      -- | Use 'strictlyOriented' as atom to denote 
      -- that the given rule is strictly oriented.
    , weaklyOriented
      -- | Use 'weaklyOriented' as atom to denote 
      -- that the given rule is weakly oriented.
    , initialStrictRules
      -- | Initial value for 'StrictRules'
      
    , StrictRules (..)
      -- | The encoding decodes to a set of strict rules.
    ) 
where

import Data.Typeable
import Termlib.Term
import Termlib.Rule
import qualified Termlib.Trs as Trs
import Qlogic.SatSolver

import Qlogic.PropositionalFormula
import Termlib.Trs (Trs, union, singleton)

data Orientation = Strict (Term,Term)
                 | Weak (Term,Term) deriving (Eq, Ord, Typeable, Show)

newtype StrictRules = Sr {trs :: Trs}

strictlyOriented :: Rule -> Orientation
strictlyOriented = Strict . toPair

weaklyOriented :: Rule -> Orientation
weaklyOriented = Weak . toPair

initialStrictRules :: StrictRules 
initialStrictRules = Sr Trs.empty

instance PropAtom Orientation

instance Decoder StrictRules Orientation where 
  add (Strict r) sr = sr {trs = singleton (fromPair r) `union` trs sr}
  add (Weak _)   sr = sr

