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

{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableInstances #-}

module Tct.Encoding.AbstractInterpretation where

import Prelude hiding ((&&))
import Qlogic.Boolean
import qualified Termlib.Rule as R
import qualified Termlib.Term as T
import qualified Termlib.Trs as Trs
import Qlogic.Semiring

class Algebra a c | a -> c where
  interpretTerm :: a -> T.Term -> c

instance (AbstrEq c b, Algebra a c) => AbstrEq T.Term (a -> b) where
  t1 .==. t2 = \a -> interpretTerm a t1 .==. interpretTerm a t2

instance (AbstrOrd c b, Algebra a c) => AbstrOrd T.Term (a -> b) where
  t1 .<. t2 = \a -> interpretTerm a t1 .<. interpretTerm a t2
  t1 .<=. t2 = \a -> interpretTerm a t1 .<=. interpretTerm a t2

ruleConstraints :: Algebra a c => (c -> c -> b) -> a -> R.Rule -> b
ruleConstraints o mi r = interpretTerm mi (R.lhs r) `o` interpretTerm mi (R.rhs r)

strictRuleConstraints :: (AbstrOrd c b, Algebra a c) => a -> R.Rule -> b
strictRuleConstraints = ruleConstraints (.>.)

weakRuleConstraints :: (AbstrOrd c b, Algebra a c) => a -> R.Rule -> b
weakRuleConstraints = ruleConstraints (.>=.)

orientOneConstraints :: (Algebra a c, AbstrOrd c b) => (c -> c -> b) -> a -> Trs.Trs -> b
orientOneConstraints o mi = bigOr . map (ruleConstraints o mi) . Trs.rules

trsConstraints :: (Algebra a c, AbstrOrd c b) => (c -> c -> b) -> a -> Trs.Trs -> b
trsConstraints o mi = bigAnd . map (ruleConstraints o mi) . Trs.rules

strictTrsConstraints :: (Algebra a c, AbstrOrd c b) => a -> Trs.Trs -> b
strictTrsConstraints = trsConstraints (.>.)

weakTrsConstraints :: (Algebra a c, AbstrOrd c b) => a -> Trs.Trs -> b
weakTrsConstraints = trsConstraints (.>=.)

relativeStrictTrsConstraints :: (Algebra a c, AbstrOrd c b) => a -> Trs.Trs -> b
relativeStrictTrsConstraints = orientOneConstraints (.>.) && trsConstraints (.>=.)

relativeStricterTrsConstraints :: (Algebra a c, AbstrOrd c b) => a -> Trs.Trs -> b
relativeStricterTrsConstraints a trs = if Trs.isEmpty incRules
                                        then relativeStrictTrsConstraints a trs
                                        else weakTrsConstraints a nonIncRules && strictTrsConstraints a incRules
  where incRules = trs Trs.\\ nonIncRules
        nonIncRules = Trs.filterRules R.isNonSizeIncreasing trs

strictOneConstraints :: (Algebra a c, AbstrOrd c b) => a -> Trs.Trs -> b
strictOneConstraints = orientOneConstraints (.>.)
