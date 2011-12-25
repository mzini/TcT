--------------------------------------------------------------------------------
-- | 
-- Module      :  Tct.Processors
-- Copyright   :  (c) Martin Avanzini <martin.avanzini@uibk.ac.at>, 
--                Georg Moser <georg.moser@uibk.ac.at>, 
--                Andreas Schnabl <andreas.schnabl@uibk.ac.at>,
-- License     :  LGPL (see COPYING)
--
-- Maintainer  :  Martin Avanzini <martin.avanzini@uibk.ac.at>
-- Stability   :  unstable
-- Portability :  unportable      
-- 
-- This module collects available /processors/ of TcT.
-- A processor 'p' is the TcT representation of a complexity techniques
-- that, given a complexity problem, constructs a complete proof for 
-- the problem. 
-- Processors are parameterised in some arguments that control the behaviour
-- of the processor, for instance, the matrix processor is parameterised 
-- in the dimension of the constructed matrix interpretation. 
-- Parameterised processors are called /processor instances/. 
--------------------------------------------------------------------------------      


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

{-# LANGUAGE CPP #-}
module Tct.Processors where

import Prelude hiding (fail, uncurry)
#include "_Processors_Imports_.hs"

-- * Built-In Processors
#include "_Processors_Defs_.hs"
#include "_Transformations_Defs_.hs"
#include "_BuiltIn_.hs"
