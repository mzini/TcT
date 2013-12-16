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
       , XmlAttribute
       , XmlDocument
         -- * Constructors
       , elt
       , strAttrib
         -- * Translations to XML for general data types
       , int
       , text
       , putXml
       , toDocument
       )
       where

-- import qualified Text.XML.HaXml.Types as Xml
-- import qualified Text.XML.HaXml.Pretty as XmlPP
-- -- import qualified Text.XML.HaXml.ByteStringPP as XmlPP

import qualified Data.ByteString.Lazy as BS
import qualified Data.Text as Txt

import Text.XML.Generator


-- import qualified Tct.Main.Version as Version

-- import qualified Text.PrettyPrint.HughesPJ as PP
type XmlContent = Xml Elem
type XmlAttribute = Xml Attr
type XmlDocument = Xml Doc


elt :: String -> [Xml Attr] -> [XmlContent] -> XmlContent
elt name attr children = xelem (Txt.pack name) $ xattrs attr <#> children


strAttrib :: String -> String -> XmlAttribute
strAttrib n s = xattr (Txt.pack n) (Txt.pack s)

int :: (Integral i) => i -> XmlContent
int i = xtext $ Txt.pack $ show $ toInteger i

text :: String -> XmlContent 
text = xtext  . Txt.pack 

          
putXml :: Renderable t => Xml t -> IO ()
putXml = BS.putStr . xrender


toDocument :: XmlContent -> XmlDocument
toDocument = doc defaultDocInfo