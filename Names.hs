-----------------------------------------------------------------------------
-- |
-- Module      :  Names
-- Copyright   :  (c) Alexander Vivian Hugh McPhail 2000, 2015, 2023
-- License     :  BSD3
--
-- Maintainer  :  haskell.vivian.mcphail <at> gmail <dot> com
-- Stability   :  provisional
-- Portability :  portable
--
-- Lambda combinators
--
-----------------------------------------------------------------------------
module Names (
  module Data.Map
  , Combinators
  , combinators
  , Constants
  , constants
  ) where

{-----------------------------------------------------------------------}

import System.IO.Unsafe

import Data.Char
import System.IO
import Data.Map
import Parsers

import qualified Prelude as P

{-----------------------------------------------------------------------}

type Constant = P.String
type Variable = P.String
type Function = P.String

type Constants = Map Variable ()
type Combinators = Map Variable Function

{-----------------------------------------------------------------------}
{- parsers -}

space :: (Parser Char a) -> Parser Char a
space = \p -> p P.. P.dropWhile isSpace

{-----------------------------------------------------------------------}

isEOL :: Char -> P.Bool
isEOL = (P.== '\n')

equals :: Parser Char Char
equals = single_symbol '='

eol :: Parser Char Char
eol = single_symbol '\n'

untilEOL :: Parser Char P.String
untilEOL = (first P.. star) (satisfy (P.not P.. isEOL))

{-----------------------------------------------------------------------}

identifier :: Parser Char Variable
identifier = (first P.. plus) (satisfy isAlpha)

{-----------------------------------------------------------------------}

function :: Parser Char Function
function = untilEOL <& eol 

doLineConstants :: Parser Char Constant
doLineConstants = (space identifier <& (untilEOL <& eol))

doLineCombinators :: Parser Char (Variable,Function)
doLineCombinators = ((space identifier <& space equals) <&> space function)

doFileConstants :: Parser Char [Constant]
doFileConstants = (first P.. plus) doLineConstants

doFileCombinators :: Parser Char [(Variable,Function)]
doFileCombinators = (first P.. plus) doLineCombinators

{-----------------------------------------------------------------------}

getFileContents :: FilePath -> P.String
getFileContents fn = unsafePerformIO (readFile fn)

{-----------------------------------------------------------------------}

loadConstants :: [Constant]
loadConstants = P.snd P.. P.head P.. doFileConstants P.$ getFileContents "constants.lam"

constants :: Constants
constants = fromList P.$ P.map (\x -> (x,())) loadConstants

loadCombinators :: [(Variable,Function)]
loadCombinators = P.snd P.. P.head P.. doFileCombinators P.$ getFileContents "combinators.lam"

combinators :: Combinators
combinators = fromList loadCombinators

{-----------------------------------------------------------------------}

test1 = lookup  "curry" combinators

{-----------------------------------------------------------------------}
{- combinators -} 

{-----------------------------------------------------------------------}
