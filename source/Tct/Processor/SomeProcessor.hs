{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TypeFamilies #-}
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

{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE TypeSynonymInstances #-}

module Tct.Processor.SomeProcessor 
    -- ( SomeProcessor
    -- , AnyProcessor
    -- , some
    -- , someInstance
    -- , anyOf
    -- , processors
    -- ) 
where

import Control.Monad (liftM)
import Text.ParserCombinators.Parsec (choice)
import Text.PrettyPrint.HughesPJ
import Termlib.Utils (PrettyPrintable (..))
import Tct.Processor
import Tct.Proof

-- data SomeProof     = forall p. (ComplexityProof p) => SomeProof p
-- data SomeInstance  = forall p. (ComplexityProof (ProofOf p) , Processor p) => SomeInstance p (InstanceOf p)

-- instance PrettyPrintable SomeProof where
--     pprint (SomeProof p) = pprint p

-- instance Answerable SomeProof where
--     answer (SomeProof p) = answer p

-- instance ComplexityProof SomeProof

-- instance Processor SomeProcessor where
--     type ProofOf    SomeProcessor = SomeProof
--     data InstanceOf SomeProcessor = SPI SomeInstance
--     name (SomeProcessor proc) = name proc
--     description (SomeProcessor proc) = description proc
--     synopsis (SomeProcessor proc) = synopsis proc
--     solve (SPI (SomeInstance _ inst)) prob = SomeProof `liftM` solve inst prob
--     fromInstance (SPI (SomeInstance proc _)) = SomeProcessor proc
--     parseProcessor_ (SomeProcessor proc) = (SPI . SomeInstance proc) `liftM` parseProcessor_ proc

-- instance PrettyPrintable SomeProcessor where
--     pprint (SomeProcessor proc) = ppheading $$ (nest 2 $ ppdescr $+$ text "" $+$ ppsyn)
--         where ppheading = text "Strategy" <+> doubleQuotes (text sname) <> text ":"
--               ppdescr = vcat [fsep $ [text w | w <- words s] | s <- descr] 
--               ppsyn = text "Usage:" $+$ text "" $+$  (nest 2 $ text $ synopsis proc)
--               sname = name proc 
--               descr = description proc 

-- some :: forall p. (ComplexityProof (ProofOf p), Processor p) => p -> SomeProcessor
-- some = SomeProcessor

-- someInstance :: forall p. (ComplexityProof (ProofOf p), Processor p) => InstanceOf p -> InstanceOf SomeProcessor
-- someInstance inst = SPI (SomeInstance (fromInstance inst) inst)



-- instance Processor AnyProcessor where
--     type ProofOf AnyProcessor = SomeProof
--     data InstanceOf AnyProcessor = OOI (InstanceOf SomeProcessor) AnyProcessor
--     name _ = "some processor" -- TODO
--     description _ = []
--     synopsis _    = ""
--     solve (OOI inst _) prob = solve inst prob
--     fromInstance (OOI _ proc) = proc
--     parseProcessor_ p@(OO ps) = do inst <- choice [ parseProcessor_ p' | p' <- ps]
--                                    return $ OOI inst p

-- anyOf :: [SomeProcessor] -> AnyProcessor
-- anyOf = OO

-- processors :: AnyProcessor -> [SomeProcessor]
-- processors (OO l) = l