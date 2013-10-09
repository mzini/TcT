{-# LANGUAGE FlexibleContexts #-}
{- | 
Module      :  Tct.Encoding.AbstractInterpretation
Copyright   :  (c) Martin Avanzini <martin.avanzini@uibk.ac.at>, 
               Georg Moser <georg.moser@uibk.ac.at>, 
               Andreas Schnabl <andreas.schnabl@uibk.ac.at>
License     :  LGPL (see COPYING)

Maintainer  :  Andreas Schnabl <andreas.schnabl@uibk.ac.at>
Stability   :  unstable
Portability :  unportable      
-}

{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableInstances #-}

module Tct.Encoding.AbstractInterpretation where

import Prelude hiding ((&&))
import Tct.Utils.PPrint (Align(..), columns)
import Qlogic.Boolean
import qualified Termlib.FunctionSymbol as F
import qualified Termlib.Variable as V
import qualified Termlib.Rule as R
import qualified Termlib.Term as T
import qualified Termlib.Trs as Trs
import Qlogic.Semiring
import Text.PrettyPrint.HughesPJ
import Termlib.Utils hiding (columns)

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

relativeStricterTrsConstraints :: (Algebra a c, AbstrOrd c b) => [R.Rule] -> a -> Trs.Trs -> b
relativeStricterTrsConstraints []       a trs = relativeStrictTrsConstraints a trs
relativeStricterTrsConstraints oblrules a trs = weakTrsConstraints a nonobltrs && strictTrsConstraints a obltrs
  where obltrs    = Trs.fromRules oblrules
        nonobltrs = trs Trs.\\ obltrs

strictOneConstraints :: (Algebra a c, AbstrOrd c b) => a -> Trs.Trs -> b
strictOneConstraints = orientOneConstraints (.>.)

pprintOrientRules :: (PrettyPrintable (c, V.Variables), AbstrOrd c Bool, Algebra a c) => a -> F.Signature -> V.Variables -> [R.Rule] -> Doc
pprintOrientRules inter sig vars rs = 
  columns [ (AlignRight, as)
          , (AlignLeft, bs)
          , (AlignLeft, cs)]
  where 
    (as, bs, cs) = unzip3 $ concatMap ppOrientRl rs
    ppOrientRl rule
      -- | '?' `elem` ord = []
      | otherwise = [ (ppIntTerm l , text " = " , pprint (il, vars))
                    , (empty       , text ord   , pprint (ir, vars))
                    , (empty       , text " = " , ppIntTerm r)
                    , nl]
      where 
        l = R.lhs rule
        r = R.rhs rule
        il = interpretTerm inter l
        ir = interpretTerm inter r
        nl = (text " ", text " ", text " ")
        ord | il .>. ir = " > "
            | il .>=. ir = " >= "
            | otherwise  = " ? "
        ppIntTerm t = brackets $ pprint (t, sig, vars)
