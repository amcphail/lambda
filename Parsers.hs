-----------------------------------------------------------------------------
-- |
-- Module      :  Parsers
-- Copyright   :  (c) Alexander Vivian Hugh McPhail 2000, 2015
-- License     :  BSD3
--
-- Maintainer  :  haskell.vivian.mcphail <at> gmail <dot> com
-- Stability   :  provisional
-- Portability :  portable
--
-- Monadic Parsers
--
-----------------------------------------------------------------------------
module Parsers (
  Parser,
  DetParser,
  --
  parse_fail,    -- Parser s a
  succeed,       -- a -> Parser s a
  epsilon,       -- Parser s [a]
  --
  satisfy,       -- (s -> Bool) -> Parser s s
  single_symbol, -- Eq s => s -> Parser s s
  token,         -- Eq s => [s] -> Parser s [s]
  --
  (<|>),         -- (Parser s a) -> (Parser s a) -> Parser s a
  (<@),          -- (Parser s a) -> (a -> b) -> Parser s b
  (<&>),         -- (Parser s a) -> (Parser s b) -> Parser s (a,b)
  (<&),          -- (Parser s a) -> (Parser s b) -> Parser s a
  (&>),          -- (Parser s a) -> (Parser s b) -> Parser s b
  (<:&>),        -- (Parser s a) -> (Parser s [a]) -> Parser s [a]
  (<&=>),        -- (Parser s a) -> (a -> Parser s b) -> Parser s b
  --
  just,          -- (Parser s a) -> Parser s a
  some,          -- (Parser s a) -> DetParser s a
  first,         -- (Parser s a) -> Parser s a
  --
  star,          -- (Parser s a) -> Parser s [a]
  plus,          -- (Parser s a) -> Parser s [a]
  bang,          -- ((Parser s a) -> Parser s [a]) -> (Parser s a) -> Parser s [a]
  --  
  optionally     -- (Parser s a) -> Parser s [a]
  ) where

{-----------------------------------------------------------------------}

type Parser symbol result = [symbol] -> [([symbol],result)]

type DetParser symbol result = [symbol] -> result

{-----------------------------------------------------------------------}

parse_fail :: Parser s a
parse_fail = \_ -> []

succeed :: a -> Parser s a
succeed v = \xs -> [(xs,v)]

epsilon :: Parser s [a]
epsilon = succeed []

{-----------------------------------------------------------------------}

satisfy :: (s -> Bool) -> Parser s s
satisfy f (x:xs) = if (f x) then [(xs,x)] else []
satisfy f _      = []

single_symbol :: Eq s => s -> Parser s s
single_symbol = \s -> satisfy (== s)

token :: Eq s => [s] -> Parser s [s]
token k xs
      | k == take n xs = [(drop n xs,k)]
      | otherwise      = []
      where n = length k

{-----------------------------------------------------------------------}

{- alternation -}
infixr 4 <|>
(<|>) :: (Parser s a) -> (Parser s a) -> Parser s a
(p1 <|> p2) xs = p1 xs ++ p2 xs

{- concatenation -}
infixr 6 <&>
(<&>) :: (Parser s a) -> (Parser s b) -> Parser s (a,b)
(p1 <&> p2) xs = [(xs2, (v1,v2)) | (xs1,v1) <- p1 xs, (xs2,v2) <- p2 xs1]

{- concatenation, discard rhs -}
infixr 6 <&
(<&) :: (Parser s a) -> (Parser s b) -> Parser s a
(p1 <& p2) xs = (p1 <&> p2 <@ fst) xs

{- concatenation, discard lhs -}
infixr 6 &>
(&>) :: (Parser s a) -> (Parser s b) -> Parser s b
(p1 &> p2) xs = (p1 <&> p2 <@ snd) xs

{- list concatenation -} 
infixr 6 <:&>
(<:&>) :: (Parser s a) -> (Parser s [a]) -> Parser s [a]
(p1 <:&> p2) xs = (p1 <&> p2 <@ (uncurry (:))) xs

{- semantic function -}
infixl 5 <@
(<@) :: (Parser s a) -> (a -> b) -> Parser s b
(p0 <@ f) xs = [(ys, f v) | (ys,v) <- p0 xs]

{- bind -}
infixr 6 <&=>
(<&=>) :: (Parser s a) -> (a -> Parser s b) -> Parser s b
(p1 <&=> p2) xs = [ ts | (xs1,v1) <- p1 xs, ts <- p2 v1 xs1 ]

{-----------------------------------------------------------------------}

just :: (Parser s a) -> Parser s a
just p = filter (null . fst) . p

some :: (Parser s a) -> DetParser s a
some p = snd . head . just p

first :: (Parser s a) -> Parser s a
first p = (take 1) . p

{-----------------------------------------------------------------------}

star :: (Parser s a) -> Parser s [a]
star p = p <:&> star p
 <|> epsilon

plus :: (Parser s a) -> Parser s [a]
plus p = p <:&> star p

bang :: ((Parser s a) -> Parser s [a]) -> (Parser s a) -> Parser s [a]
bang p = first . p

optionally :: (Parser s a) -> Parser s [a]
optionally p = p <@ (\x -> [x])
       <|> epsilon

{-----------------------------------------------------------------------}
