{- | 
Module      :  Tct.Encoding.HomomorphicInterpretation
Copyright   :  (c) Martin Avanzini <martin.avanzini@uibk.ac.at>, 
               Georg Moser <georg.moser@uibk.ac.at>, 
               Andreas Schnabl <andreas.schnabl@uibk.ac.at>
License     :  LGPL (see COPYING)

Maintainer  :  Andreas Schnabl <andreas.schnabl@uibk.ac.at>
Stability   :  unstable
Portability :  unportable      
-}

{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableInstances #-}

module Tct.Encoding.HomomorphicInterpretation where

import Tct.Encoding.AbstractInterpretation
import qualified Termlib.FunctionSymbol as F
import qualified Termlib.Term as T
import qualified Termlib.Variable as V

class Interpretation a c | a -> c where
  interpretFun :: a -> F.Symbol -> [c] -> c
  interpretVar :: a -> V.Variable -> c

instance Interpretation a c => Algebra a c where
  interpretTerm a (T.Var v)    = interpretVar a v
  interpretTerm a (T.Fun f ts) = interpretFun a f ts'
                                 where ts' = map (interpretTerm a) ts
