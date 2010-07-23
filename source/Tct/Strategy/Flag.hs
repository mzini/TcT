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
module Tct.Strategy.Flag 
    ( Flag (..) 
    , Flags (..)
    , noFlags
    , stringFlag
    , natFlag
    , boolFlag
    , choiceFlag
    , stringFlagValue
    , natFlagValue
    , boolFlagValue
    , choiceFlagValue
    , parseFlag
    , parseFlags
    )
where
import Control.Monad (mplus, liftM)
import Text.ParserCombinators.Parsec
import Text.PrettyPrint.HughesPJ hiding (char)
import qualified Data.List as List
import qualified Data.Maybe as Maybe

import Termlib.Utils (PrettyPrintable(..), paragraph)

import Tct.Strategy.Parse hiding (brackets)

data FlagArg = Boolean Bool
             | Natural Int
             | StringLit String 
             | ChoiceLit String [String]
               deriving (Eq, Show)

data Flag = Flag { flagName  :: String
                 , flagArg   :: FlagArg
                 , flagDescr :: String}
            deriving (Eq, Show)

newtype Flags = Flags [Flag] deriving (Eq, Show)

noFlags :: Flags
noFlags = Flags []

-- | Constructors
stringFlag :: String -> String -> String -> Flag
stringFlag n v d = Flag n (StringLit v) d

choiceFlag :: String -> String -> [String] -> String -> Flag
choiceFlag n deflt others d = Flag n (ChoiceLit deflt others) d

boolFlag :: String -> Bool -> String -> Flag
boolFlag n v d = Flag n (Boolean v) d

natFlag :: String -> Int -> String -> Flag
natFlag n v d = Flag n (Natural v) d

-- | Accessors

lookupFlag :: String -> Flags -> Maybe Flag
lookupFlag n (Flags fl) = List.find byName fl
  where byName f = n == flagName f

flagValue :: (Flag -> Maybe v) -> Flags -> Flags -> String -> v
flagValue extract defaults parsedFlags n =
    
  Maybe.fromMaybe (error $ List.concat $ List.intersperse " " ["Strategy.Flag.flagValue", show defaults, show parsedFlags, show n])
         $ (lookupFlag n parsedFlags `mplus` lookupFlag n defaults) >>= extract

boolFlagValue :: Flags -> Flags -> String -> Bool
boolFlagValue = flagValue extract
  where extract f = case flagArg f of 
                      Boolean b -> Just b
                      _         -> Nothing

stringFlagValue :: Flags -> Flags -> String -> String
stringFlagValue = flagValue extract 
  where extract f = case flagArg f of 
                      StringLit s -> Just s
                      _           -> Nothing

natFlagValue :: Flags -> Flags -> String -> Int
natFlagValue = flagValue extract 
  where extract f = case flagArg f of 
                      Natural n -> Just n
                      _         -> Nothing

choiceFlagValue :: Flags -> Flags -> String -> String
choiceFlagValue = flagValue extract 
  where extract f = case flagArg f of 
                      ChoiceLit n _ -> Just n
                      _             -> Nothing

-- | parsing and pretty printing

parseFlag :: Flags -> CharParser st Flag
parseFlag defaults@(Flags fs) = 
  do _ <- char ':' 
     n <- identifier
     whiteSpace
     case lookupFlag n defaults of 
       Just f@(Flag _ (Boolean _) _)      -> parseFlag' f bool Boolean
       Just f@(Flag _ (StringLit _) _)    -> parseFlag' f (try stringLit <|> identifier) StringLit
       Just f@(Flag _ (Natural _) _)      -> parseFlag' f natural Natural
       Just f@(Flag _ (ChoiceLit a as) _) -> parseFlag' f (eltOf as') (\ a' -> ChoiceLit a' as)
           where as' = reverse $ List.sort (a:as)
       Nothing                            -> unexpected $ "flag " ++ n ++ "; choose one of: " 
                                            ++ List.concat (List.intersperse ", " [flagName f | f <- fs])
    where parseFlag' f parser mk = do v <- (parser <?> (show $ ppFlagType f))
                                      return $ f{flagArg=mk v}


parseFlags :: Flags -> CharParser st Flags
parseFlags defaults = Flags `liftM` many (parseFlag defaults >>= \f -> whiteSpace >> return f)


instance PrettyPrintable FlagArg where 
  pprint (Boolean True)  = text "On"
  pprint (Boolean False) = text "Off"
  pprint (Natural n)     = text $ show n
  pprint (StringLit n)   = text $ n
  pprint (ChoiceLit n _) = text $ n


instance PrettyPrintable (Flags) where
    pprint (Flags fl) = fcat [ ppflag f | f <- fl]
        where ppflag f@(Flag n v d) = ppflagName n <+> ppFlagType f 
                                      $$ (nest 2 $ paragraph $ d ++ " The default value is set to \"" ++ show (pprint v) ++ "\".")
              ppflagName n = text ":" <> text n

ppFlagType :: Flag -> Doc
ppFlagType (Flag _ (Natural _) _)     = text "<sum>"
ppFlagType (Flag _ (StringLit _) _)    = text "<string>"
ppFlagType (Flag _ (Boolean _) _)      = text "<On|Off>" 
ppFlagType (Flag _ (ChoiceLit a as) _) = brackets $ hcat $ punctuate (text "|") [text c | c <- a:as]



