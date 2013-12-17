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
-- This module provides Xml-encodings of common data structures
----------------------------------------------------------------------------------

module Tct.Utils.Xml.Encoding 
    (
    -- * Translations to XML for termlib data types         
    symbol
    , variable
    , term 
    , rule
    , rules
    , strategy
    , startTerms
    , complexityProblem
    , proofDocument
    )
where 

import qualified Data.Set as Set

import Tct.Utils.Xml
import Tct.Main.Version (version)
import qualified Termlib.FunctionSymbol as F
import qualified Termlib.Term as T
import qualified Termlib.Signature as Sig
import qualified Termlib.Variable as V
import qualified Termlib.Rule as R
import qualified Termlib.Trs as Trs
import qualified Termlib.Problem as Prob
import qualified Tct.Certificate as C
import qualified Tct.Proof as Proof
import Termlib.Utils (PrettyPrintable (..))


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
  elt "funapp" [] $ [symbol f sig] ++ [elt "arg" [] [term t sig vs] | t <- ts]

rule :: R.Rule -> Maybe Int -> F.Signature -> V.Variables -> XmlContent  
rule r mid sig vs = 
  elt "rule" attribs
  [ elt "lhs" [] [term (R.lhs r) sig vs]
  , elt "rhs" [] [term (R.rhs r) sig vs]]  
    where 
      attribs = maybe [] (\n -> [ strAttrib "rid" (show n) ]) mid
          
  
rules :: Trs.Trs -> F.Signature -> V.Variables -> XmlContent
rules rs sig vs = elt "rules" [] [ rule r Nothing sig vs | r <- Trs.rules rs ]

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

answer :: Proof.Answer -> XmlContent  
answer Proof.NoAnswer          = elt "no" [] []
answer Proof.MaybeAnswer       = elt "maybe" [] []
answer Proof.TimeoutAnswer     = elt "timeout" [] []
answer (Proof.CertAnswer cert) = 
  elt "certified" [] [ elt "lowerbound" [] [complexity $ C.lowerBound cert] 
                     , elt "upperbound" [] [complexity $ C.upperBound cert]]
  
strategy :: Prob.Strategy -> XmlContent
strategy Prob.Innermost = elt "innermost" [] []
strategy Prob.Full      = elt "full" [] []
strategy Prob.Outermost = elt "outermost" [] []
strategy _              = error "Xml.ComplexityInput: unsupported strategy contextsensitive"

startTerms :: Prob.StartTerms -> F.Signature -> XmlContent
startTerms (Prob.TermAlgebra fs) sig =
  elt "derivationalComplexity" [] [signature fs sig]
startTerms (Prob.BasicTerms ds cs) sig =
  elt "runtimeComplexity" [] [signature cs sig, signature ds sig]
  
complexityProblem :: Prob.Problem -> Proof.Answer -> XmlContent
complexityProblem prob ans = 
  elt "complexityInput" [] [ elt "relation" [] $ 
                             concat [ trs "strictTrs" Prob.strictTrs
                                    , trs "weakTrs" Prob.weakTrs
                                    , trs "strictDPs" Prob.strictDPs
                                    , trs "weakDPs" Prob.weakDPs]
                           , elt "complexityMeasure" [] [startTerms (Prob.startTerms prob) sig]
                           , elt "strategy" [] [strategy $ Prob.strategy prob]
                           , elt "answer" [] [answer ans]]
    where trs n f = 
            case f prob of 
              rs | Trs.isEmpty rs -> []
                 | otherwise -> [elt n [] [ rules rs sig vs ]]
          sig = Prob.signature prob
          vs  = Prob.variables prob

          
proofDocument :: Proof.ComplexityProof proof => Prob.Problem -> [(R.Rule, Bool)] -> proof -> Proof.Answer -> XmlDocument
proofDocument prob rulelist proof ans = 
    toDocument $ elt "tctOutput" attribs [inpt, Proof.toXml proof, vers ]
        where
          attribs = []
          inpt = elt "input" [] [ elt "trs" [] [elt "rules" [] [ rule r Nothing sig vs | (r,False) <- rulelist ]]
                                , elt "strategy" [] [strategy $ Prob.strategy prob]                                              
                                , elt "relativeRules" [] [ elt "rules" [] [rule r Nothing sig vs | (r,True) <- rulelist ]]
                                , elt "complexityMeasure" [] [startTerms (Prob.startTerms prob) sig]
                                , elt "answer" [] [answer ans]]
          vers = elt "version" [] [text $ version]
          vs = Prob.variables prob
          sig = Prob.signature prob
               
  -- Xml.Document prolog symtab el misc
  --   where prolog = Xml.Prolog (Just xmlversion) [Xml.PI ("xml-stylesheet", style)] Nothing []
  --           where xmlversion = Xml.XMLDecl "1.0" Nothing Nothing
  --                 style = "type=\"text/xsl\" href=\"tctpfHTML.xsl\""
  --         el = Xml.Elem (Xml.N "tctOutput") attribs [inpt, Proof.toXml proof, version ]
  --           where attribs = [ (Xml.N "xmlns:xsi", Xml.AttValue [Left "http://www.w3.org/2001/XMLSchema-instance"])
  --                           -- , (Xml.N "xsi", Xml.AttValue [Left "http://cl-informatik.uibk.ac.at/software/tct/include/tctpf.xsd"])
  --                           ]
  --                 inpt     = 
  --                 version  = elt "version" [] [text $ Version.version]
                  
  --         misc = []
  --         symtab = []

