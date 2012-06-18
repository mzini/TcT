{-# LANGUAGE TypeFamilies #-}
{- | 
Module      :  Tct.Method.ToInnermost
Copyright   :  (c) Martin Avanzini <martin.avanzini@uibk.ac.at>, 
               Georg Moser <georg.moser@uibk.ac.at>, 
               Andreas Schnabl <andreas.schnabl@uibk.ac.at>
License     :  LGPL (see COPYING)

Maintainer  :  Martin Avanzini <martin.avanzini@uibk.ac.at>
Stability   :  unstable
Portability :  unportable      

Switches from full to innermost rewriting for overlay, right-linear TRSs
-}

module Tct.Method.ToInnermost
       ( toInnermost
         -- * Proof Object
       , ToInnermostProof (..)
         -- * Processor
       , toInnermostProcessor
       , ToInnermost
       ) where
    
import Text.PrettyPrint.HughesPJ hiding (empty)

import Tct.Utils.Enum (enumeration')

import qualified Tct.Processor.Transformations as T
import qualified Tct.Processor as P
import Tct.Processor.Args as A

import Termlib.Utils
import Termlib.Trs (isRightLinear, isOverlay)    
import qualified Termlib.Problem as Prob


data ToInnermostProof = ToiNonOverlay
                      | ToiNonRightLinear
                      | ToiSuccess
                        
data ToInnermost = ToInnermost deriving Show
                        
instance PrettyPrintable ToInnermostProof where
  pprint ToiNonRightLinear = text "The input is not right linear." 
  pprint ToiNonOverlay     = text "The input is not an overlay." 
  pprint ToiSuccess        = paragraph ("The input is overlay and right-linear." 
                                        ++ "Switching to innermost rewriting.")
                             
instance T.TransformationProof ToInnermost where
  answer = T.answerFromSubProof
  pprintTProof _ _ p _ = pprint p
  
  
instance T.Transformer ToInnermost where
    name ToInnermost        = "toInnermost"
    description ToInnermost = ["Switches to innermost rewriting on overlay and right-linear input."]

    type ArgumentsOf ToInnermost = A.Unit
    type ProofOf ToInnermost = ToInnermostProof
    
    arguments ToInnermost = A.Unit

    transform _ prob 
         | not (isRightLinear rs) = return $ T.NoProgress ToiNonRightLinear
         | not (isOverlay rs)     = return $ T.NoProgress ToiNonOverlay
         | isInnermost          = return $ T.NoProgress ToiSuccess
         | otherwise            = return $ T.Progress ToiSuccess (enumeration' [prob'])
        where rs          = Prob.allComponents prob
              prob'       = prob { Prob.strategy = Prob.Innermost }
              isInnermost = Prob.strategy prob == Prob.Innermost


toInnermostProcessor :: T.Transformation ToInnermost P.AnyProcessor
toInnermostProcessor = T.Transformation ToInnermost

toInnermost :: T.TheTransformer ToInnermost
toInnermost = T.Transformation ToInnermost `T.withArgs` ()