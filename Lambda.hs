-----------------------------------------------------------------------------
-- |
-- Module      :  Lambda
-- Copyright   :  (c) Alexander Vivian Hugh McPhail 2000, 2015
-- License     :  BSD3
--
-- Maintainer  :  haskell.vivian.mcphail <at> gmail <dot> com
-- Stability   :  provisional
-- Portability :  portable
--
-- Lambda evaluator
--
-----------------------------------------------------------------------------

module Lambda (
       Term(Var,Lam,App),
       --
       term, -- Parser Char Term
               normal,  -- String -> String
               --
               parse,   -- DetParser Char Term (i.e. String -> Term)
               eval,    -- Term -> Term
               unparse  -- Term -> String
              )  where

{-----------------------------------------------------------------------}
{- imports -}

import Data.Char
import qualified Data.List as L
import qualified Data.Map as M
import Parsers
import Combinators

{-----------------------------------------------------------------------}
{- data types -}

type Name = String

data Term = Var Name
          | Lam Name Term
  | App Term Term
  deriving (Eq,Read)

{-----------------------------------------------------------------------}

instance Show Term where
    show t = unparse t

{-----------------------------------------------------------------------}
{- READ -}

{-----------------------------------------------------------------------}
{- parsers -}

space :: (Parser Char a) -> Parser Char a
space = \p -> p . dropWhile isSpace

{-----------------------------------------------------------------------}

lbra :: Parser Char Char
lbra = single_symbol '('

rbra :: Parser Char Char
rbra = single_symbol ')'

bracket :: (Parser Char a) -> Parser Char a 
bracket = \p -> space lbra &> p <& space rbra

opt_bra :: (Parser Char a) -> Parser Char a
opt_bra = \p -> bracket p <|> p

{-----------------------------------------------------------------------}

identifier :: Parser Char Name
identifier = (first . plus) (satisfy isAlpha)

lambda :: Parser Char Char
lambda = single_symbol '^'

dot :: Parser Char Char
dot = single_symbol '.'

{-----------------------------------------------------------------------}

var :: Parser Char Name
var = space identifier

abst :: Parser Char Name
abst = space lambda &> var <& space dot

{-----------------------------------------------------------------------}
{- fully bracketed expressions -}
{-
Lambda expressions have the following grammar:

Term = ( Var )
     | ( Abs Term )
     | ( Term ) ( Term )
-}

fb_term :: Parser Char Term
fb_term = bracket var <@ Var
         <|> bracket (abst <&> fb_term) <@ (\(n,t) -> (Lam n t))
         <|> bracket fb_term <&> bracket fb_term <@ (\(t1,t2) -> (App t1 t2))
       
{-----------------------------------------------------------------------}
{-
 we want to add:

left associativity for lambda abstraction
right associativity for function application     
optional bracketing
application binds tighter than abstraction

so we now have:

Term    = [Opt_Bra Basic]+
Basic   = Var
        | PLambda
| ( Term )
PLambda = Abs+ Term
        | Lambda [Space Var]+ Dot Term

-}

parse_lambda :: Parser Char Term
parse_lambda = plus abst <&> term <@ (\(ns,t) -> apply_lam ns t) 
               <|> (space lambda &> plus (opt_bra var) <& space dot) 
                   <&> term <@ (\(ns,t) -> apply_lam ns t)
     where
         apply_lam [n]    t = Lam n t
         apply_lam (n:ns) t = Lam n (apply_lam ns t)

basic :: Parser Char Term
basic = var <@ Var
        <|> parse_lambda
        <|> bracket term

term :: Parser Char Term
term = plus (opt_bra basic) <@ (\bs -> apply_app bs)
   where
       apply_app  (l:[])   = l
       apply_app  (l:m:[]) = App l m
       apply_app  (l:m:ns) = apply_app ((App l m):ns)

{-----------------------------------------------------------------------}
{- calls the appropriate parser -}

parse :: DetParser Char Term
parse = snd . head . term

{-----------------------------------------------------------------------}
{- EVALUATE -}

{-----------------------------------------------------------------------}
{- a stock of variables -}

fresh :: [Name]
fresh = [ "_" ++ (show x) | x <- [1..] ]

{-----------------------------------------------------------------------}
{- the set of free variables -}

frees :: Term -> [Name]
frees (Var x)   = [x]
frees (Lam x n) = L.delete x (frees n)
frees (App m n) = combine (frees n) (frees m) where
  combine []     n    = n
  combine m      []   = m 
  combine (m:ms) n  
    | elem m n  = combine ms n
    | otherwise = m : (combine ms n)

{-----------------------------------------------------------------------}
{- the substitution algorithm -}

subst :: Term -> Name -> Term -> Term
subst n x m = snd (subst' fresh n x m)

subst' :: [Name] -> Term -> Name -> Term -> ([Name],Term)
subst' f        n x (Var y)
     | x == y                   = (f,n)
     | otherwise                = (f,(Var y))
subst' f        n x (App l m)   = let (f',m')   = (subst' f  n x l)
                                      (f'',n')  = (subst' f' n x m)
                                  in (f'',(App m' n'))
subst' f@(z:fs) n x (Lam y m)
     | (not (elem y (frees n)))
       && (x /= y)              = let (f',m')   = (subst' f n x m)
                                in (f',(Lam y m'))
     | otherwise                = let (f',m')   = (subst' fs (Var z) y m)
                                      (f'',m'') = (subst' f' n       x m')
                                  in (f'',(Lam z m''))

{-----------------------------------------------------------------------}
{- reduction strategies -}

{- beta reduction -}

beta_reduce :: [Name] -> Term -> (Bool,([Name],Term))
beta_reduce f (App (Lam x m) n) = (True,subst' f n x m)
beta_reduce _ _                 = error "Lambda:beta_reduce"

{- mu reduction -}

mu_reduce :: CombinatorStore -> Term -> (Bool,Term)
mu_reduce c t@(Var v)
  | M.member v c   = (True,parse ((\(Just x) -> x) (M.lookup v c)))
  | otherwise      = (False,t)
--mu_reduce c t@(Var n)      = (False,t)
mu_reduce _ _              = error "Lambda:mu_reduce"

{- eta reduction -}

eta_reduce :: Term -> (Bool,Term)
eta_reduce t@(Lam x (App m (Var y)))
    | x == y && (not $ elem y $ frees m) = (True,m)
    | otherwise                          = (False,t)
eta_reduce _                             = error "Lambda:eta_reduce"

{-----------------------------------------------------------------------}
{- functions to check whether a reduction was performed -}

recurse_check :: [Name] -> CombinatorStore
      -> Bool -> Term -> Term -> Term
      -> ([Name] -> CombinatorStore -> Term -> (Bool,([Name],Term)))
      -> (Bool,([Name],Term))
recurse_check fs c True ts _  n _ = (True,(fs,App ts n))
recurse_check fs c _    _  t1 n f = let (red,(fs',ns)) = f fs c n 
 in  (red,(fs',App t1 ns))

bet_check :: [Name] -> CombinatorStore -> Term -> (Bool,([Name],Term))
bet_check fs c t@(App    (Lam _ _) n) = beta_reduce fs t
bet_check fs c   (App t1@(Var _)   n) = let (bet_red,(fs',ns)) = bet_check fs c n
    in  (bet_red,(fs',App t1 ns))
bet_check fs c t@(App t1@(App _ _) n) = let (bet_red,(fs',ts)) = bet_check fs c t1
    in  recurse_check fs' c bet_red ts t1 n bet_check
bet_check fs c t                      = (False,(fs,t))

mu_check :: [Name] -> CombinatorStore -> Term -> (Bool,([Name],Term))
mu_check fs c t@(App t1@(Var _)   n) = let (mu_red,ts) = mu_reduce c t1
           in recurse_check fs c mu_red ts t1 n mu_check
mu_check fs c t@(App t1@(App _ _) n) = let (mu_red,(fs',ts)) = mu_check fs c t1
             in recurse_check fs' c mu_red ts t1 n mu_check
mu_check fs c t                      = (False,(fs,t))

eta_check :: [Name] -> CombinatorStore -> Term -> (Bool,([Name],Term))
eta_check fs c t@(Lam _ (App _ (Var _))) = (\(b,t') -> (b,(fs,t'))) $ eta_reduce t
eta_check fs _ t                         = (False,(fs,t))

{-----------------------------------------------------------------------}
{- normal order evaluation (leftmost, outermost) -}

normal_order :: [Name] -> CombinatorStore -> Term -> Term
--normal_order c t = let (_,ms) = eta_check c $ normal_order' c t
--in ms
normal_order = normal_order'

normal_order' :: [Name] -> CombinatorStore -> Term -> Term
normal_order' _  _ t@(Var _)   = t
normal_order' fs c t@(Lam x m) = Lam x (normal_order' fs c m)
normal_order' fs c t@(App l m) = let (mu_red,(fs',ms)) = mu_check fs c t
 in if (mu_red) 
    then normal_order' fs' c ms  
    else let (bet_red,(fs'',bs)) = bet_check fs c t 
          in if (bet_red)   
then normal_order' fs'' c bs
      else bs

{-----------------------------------------------------------------------}
{- evaluation -}

eval :: Term -> Term
eval = normal_order  fresh combinators

{-----------------------------------------------------------------------}
{- PRINT -}

{-----------------------------------------------------------------------}

{- 
   should change the printers to use a monadic kinda thing, like the 
   parsers, so that the output setting gets passed around implicity
   --
   maybe an outer type of the parser output should contain the input
   format, so that the output matches. For example, if the input begins
   with a "$" then its latex, otherwise ascii
-}

{-----------------------------------------------------------------------}
{- modal output constants -}

start :: String -> String
start "ascii" = ""
start "latex" = "$"

finish :: String -> String
finish "ascii" = ""
finish "latex" = "$"

sp :: String -> String
sp "ascii" = " "
sp "latex" = "\\,"

lam :: String -> String
lam "ascii" = "^"
lam "latex" = "\\lambda "

{-----------------------------------------------------------------------}
{- printing helpers -}

print_bra :: String -> String
print_bra = \t -> "(" ++ t ++ ")"

print_var :: String -> Name -> String
print_var "latex" n
  | '_' == head n = "t_" ++ tail n
  | otherwise     = n
print_var "ascii" n       = n
print_var _       _       = error "Lambda:print_var"

print_lam :: String -> Term -> String
print_lam p (Lam n t) = let (lams,ts) = unpack p t
                        in lam p ++ join n lams ++ "." ++ _print' p ts
    where
        unpack p (Lam n t) = let (lams,ts) = unpack p t
                             in (n:lams,ts)
        unpack _ t         = ([],t)
        join  n []         = print_var p n
        join  n ls         = print_var p n ++ join' ls
        join' []           = ""
        join' (l:ls)       = sp p ++ print_var p l ++ join' ls
print_lam _ _         = error "Lambda:print_lam"

{-----------------------------------------------------------------------}
{- the main printing functions -}

_print'' :: String -> Term -> String
_print'' p t@(Lam _ _) = print_bra (_print' p t)
_print'' p t           = _print' p t

_print' :: String -> Term -> String
_print' p   (Var n)                 = print_var p n
_print' p t@(Lam _ _)               = print_lam p t
_print' p t@(App t1   t2@(App _ _)) = _print' p t1 ++ print_bra (_print' p t2) 
_print' p t@(App t1   t2@(Var _))   = _print'' p t1 ++ sp p ++ _print' p t2  
_print' p t@(App t1   t2)           = _print'' p t1 ++ _print'' p t2 

_print :: String -> Term -> String
_print p t = start p ++ _print' p t ++ finish p

{-----------------------------------------------------------------------}
{- printers -}

ascii_print :: Term -> String
ascii_print = _print "ascii"

latex_print :: Term -> String
latex_print = _print "latex"

{-----------------------------------------------------------------------}
{- unparser -}

unparse :: Term -> String
unparse = ascii_print

{-----------------------------------------------------------------------}
{- read, eval, print -}

normal :: String -> String
normal = unparse . eval . parse

{-----------------------------------------------------------------------}
{- the main function -}

main :: IO ()
main = do
  putStr "lambda term? "
  input <- getLine
  case input of
       "quit" -> putStr "bye.\n"
       _      -> do putStr ("-> " ++ normal input ++ "\n")
  main

{-----------------------------------------------------------------------}

test1 = "^f x.f ((^x y.y) f x)"
test2 = parse test1
