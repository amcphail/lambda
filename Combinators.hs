-----------------------------------------------------------------------------
-- |
-- Module      :  Combinators
-- Copyright   :  (c) Alexander Vivian Hugh McPhail 2000, 2015
-- License     :  BSD3
--
-- Maintainer  :  haskell.vivian.mcphail <at> gmail <dot> com
-- Stability   :  provisional
-- Portability :  portable
--
-- Lambda combinators
--
-----------------------------------------------------------------------------
module Combinators (
  module Data.Map
  , CombinatorStore
  , combinators
  ) where

{-----------------------------------------------------------------------}

import System.IO.Unsafe

import Data.Char
import System.IO
import Data.Map
import Parsers

import qualified Prelude as P

{-----------------------------------------------------------------------}

type Variable = P.String
type Function = P.String

type CombinatorStore = Map Variable Function

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

doLine :: Parser Char (Variable,Function)
doLine = ((space identifier <& space equals) <&> space function)

doFile :: Parser Char [(Variable,Function)]
doFile = (first P.. plus) doLine

{-----------------------------------------------------------------------}

getFileContents :: FilePath -> P.String
getFileContents fn = unsafePerformIO (readFile fn)

{-----------------------------------------------------------------------}

loadVariables :: [(Variable,Function)]
loadVariables = P.snd P.. P.head P.. doFile P.$ getFileContents "variables.lam"

combinators :: CombinatorStore
combinators = fromList loadVariables

{-----------------------------------------------------------------------}

test1 = lookup  "curry" combinators

{-----------------------------------------------------------------------}
{- combinators -} 

{-----------------------------------------------------------------------}
