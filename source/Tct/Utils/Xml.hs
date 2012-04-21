----------------------------------------------------------------------------------
-- |
-- Module      :  Tct.Utils.Xml
-- Copyright   :  (c) Martin Avanzini <martin.avanzini@uibk.ac.at>, 
--                Georg Moser <georg.moser@uibk.ac.at>, 
--                Andreas Schnabl <andreas.schnabl@uibk.ac.at>
-- License     :  LGPL (see COPYING)
-- Maintainer  :  Martin Avanzini <martin.avanzini@uibk.ac.at>
-- Stability   :  unstable
-- Portability :  unportable      
--
-- This module provides utilities for Xml output.
----------------------------------------------------------------------------------

module Tct.Utils.Xml 
       ( XmlContent
         -- ^ Constructors
       , elt
         -- ^ Translations to XML for general data types
       , int
       , text
         -- ^ Translations to XML for termlib data types         
       , symbol
       , variable
       , term 
       , rule
       , rules
       , complexityInput
       )
       where

import qualified Text.XML.HaXml.Types as Xml
import qualified Data.Set as Set
import qualified Tct.Certificate as C

import qualified Termlib.FunctionSymbol as F
import qualified Termlib.Term as T
import qualified Termlib.Signature as Sig
import qualified Termlib.Variable as V
import qualified Termlib.Rule as R
import qualified Termlib.Trs as Trs
import qualified Termlib.Problem as Prob

import Termlib.Utils (PrettyPrintable (..))

type XmlContent = Xml.Content ()

elt :: String -> [Xml.Attribute] -> [XmlContent] -> XmlContent
elt name attribs children = Xml.CElem (Xml.Elem (Xml.N name) attribs children) ()

int :: (Integral i) => i -> XmlContent
int i = Xml.CString False (show $ toInteger i) ()

text :: String -> XmlContent 
text s = Xml.CString True s ()

variable :: V.Variable -> V.Variables -> XmlContent
variable v vs = elt "var" [] [text $ show $ pprint (v, vs)]

symbol :: F.Symbol -> F.Signature -> XmlContent
symbol f sig = mark $ label $ elt "name" [] [text $ Sig.attribute F.symIdent f sig ]
  where mark c | F.isMarked sig f = elt "sharp" [] [c]
               | otherwise        = c 
        label c = 
          case F.symbolLabel sig f of
            Nothing               -> c
            Just (F.NatLabel i)   -> c `labelWith` [elt "numberLabel" [] [int i]]
            Just (F.RootLabel gs) -> c `labelWith` [elt "symbolLabel" [] [symbol g sig | g <- gs] ]
        c `labelWith` ls = elt "labeledSymbol" [] [ elt "symbol" [] [c]
                                                  , elt "label" [] ls ]

term :: T.Term -> F.Signature -> V.Variables -> XmlContent
term (T.Var v   ) _   vs = variable v vs
term (T.Fun f ts) sig vs = 
  elt "funapp" [] [symbol f sig
                  , elt "arg" [] [term t sig vs | t <- ts]]
  
rule :: R.Rule -> F.Signature -> V.Variables -> XmlContent  
rule r sig vs = 
  elt "rule" []
  [ elt "lhs" [] [term (R.lhs r) sig vs]
  , elt "rhs" [] [term (R.rhs r) sig vs]]  
  
rules :: Trs.Trs -> F.Signature -> V.Variables -> XmlContent
rules rs sig vs = elt "rules" [] [ rule r sig vs | r <- Trs.rules rs ]

signature :: Set.Set F.Symbol -> F.Signature -> XmlContent
signature fs sig = 
  elt "signature" [] [ elt "symbol" [] [ symbol f sig
                                       , elt "arity" [] [int (F.arity sig f) ]  ]
                     | f <- Set.toList fs ]

complexity :: C.Complexity -> XmlContent
complexity (C.Poly Nothing)   = elt "polynomial" [] []
complexity (C.Poly (Just dg)) = elt "polynomial" [] [int dg]
complexity (C.Exp Nothing)    = elt "exponential" [] []
complexity (C.Exp (Just dg))  = elt "exponential" [] [int dg]
complexity C.Supexp           = elt "superexponential" [] []
complexity C.Primrec          = elt "primitiverecursive" [] []
complexity C.Multrec          = elt "multiplerecursive" [] []
complexity C.Rec              = elt "recursive" [] []
complexity C.Unknown          = elt "unknown" [] []

complexityInput :: Prob.Problem -> C.Complexity -> XmlContent
complexityInput prob ub = 
  elt "complexityInput" [] [trsInput, measure, complexity ub]
    where trsInput = elt "trsInput" [] $ concat
            [ trs
            , strat
            , rel ]
                     
          measure =
            case Prob.startTerms prob of 
              Prob.TermAlgebra fs -> 
                elt "derivationalComplexity" [] [signature fs sig]
              Prob.BasicTerms ds cs ->
                elt "runtimeComplexity" [] [signature cs sig, signature ds sig]

          trs = [elt "trs" [] [rules strs sig vs]]
          rel | Trs.isEmpty wtrs = []
              | otherwise        = [elt "relativeRules" [] [rules strs sig vs]]
          strat = 
            case Prob.strategy prob of 
              Prob.Innermost -> [elt "strategy" [] [elt "innermost" [] []]]
              Prob.Innermost -> []
              _              -> error "Xml.ComplexityInput: unsupported strategy"

          sig = Prob.signature prob
          vs  = Prob.variables prob
          strs = Prob.strictTrs prob
          wtrs = Prob.weakTrs prob
