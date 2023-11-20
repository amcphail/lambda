-----------------------------------------------------------------------------
-- |
-- Module      :  Lambda
-- Copyright   :  (c) Alexander Vivian Hugh McPhail 2000, 2015, 2023
-- License     :  BSD3
--
-- Maintainer  :  haskell.vivian.mcphail <at> gmail <dot> com
-- Stability   :  provisional
-- Portability :  portable
--
-- Lambda evaluator
--
-----------------------------------------------------------------------------

module Main (
       main,
       Term(Con,Var,Lam,App),
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

import Control.Monad.State

import Data.Char
import qualified Data.List as L
import qualified Data.Map as M
import Parsers
import Names
import System.IO

{-----------------------------------------------------------------------}
{- data types -}

type Name = String

data Term = Con Name
          | Var Name
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
{- a monad to encapsulate variables -}

data Names = ND {
  combs :: M.Map Name Term
  , consts :: M.Map Name ()
  , vars :: [Name] }
  
newtype VM a = MVM { runVariableMonad :: Names -> (a,Names) }

instance Monad VM where
    (MVM p) >>= q = MVM (\s -> let (x,n')   = p s
                                   MVM g    = q x
                                   (x',n'') = g n'
                               in (x',n''))

instance Functor VM where
  fmap f (MVM g) = MVM (\s -> let (a,s') = g s in (f a,s'))
  
instance Applicative VM where
  pure x = MVM (\s -> (x,s))
  
  (MVM f) <*> (MVM x) = MVM (\s -> let (f',s') = f s
                                       (x',s'') = x s'
                                   in (f' x',s''))
  

instance MonadFail VM where
  fail = error "Variable Monad"
  
instance MonadState Names VM where
  get = MVM (\fs -> (fs,fs))
  put fs = MVM (\_ -> ((),fs))

next :: VM Name
next = do
       (ND cb ct (f:fs)) <- get 
       put (ND cb ct fs)
       return f

combinator :: Name -> VM (Maybe Term)
combinator n = do
  cb <- gets combs
  return $ M.lookup n cb

isJust :: Maybe a -> Bool
isJust Nothing  = False
isJust (Just _) = True

constant :: Name -> VM Bool
constant n = do
  ct <- gets consts
  return $ M.member n ct
  
{-----------------------------------------------------------------------}
{- the set of free variables -}

frees :: Term -> [Name]
frees (Con _) = []
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

--subst :: Term -> Name -> Term -> Term
--subst n x m = fst $ runVariableMonad (subst' n x m) fresh

subst' :: Term -> Name -> Term -> VM Term
subst' n x (Con c)     = return $ Con c
subst' n x (Var y)
     | x == y          = return n
     | otherwise       = return $ Var y
subst' n x (App l m)   = do
                         l' <- subst' n x l
                         m' <- subst' n x m
                         return $ App l' m'
subst' n x (Lam y m)
     | (not (elem y (frees n)))
       && (x /= y)              = do
                                  m' <- subst' n x m
                                  return $ Lam y m'
     | otherwise                = do
                                  z <- next
                                  m' <- subst' (Var z) y m
                                  m'' <- subst' n x m'
                                  return $ Lam z m''

{-----------------------------------------------------------------------}
{- reduction strategies -}

{- beta reduction -}

beta_reduce :: Term -> VM (Bool,Term)
beta_reduce (App (Lam x m) n) = do
                                b <- subst' n x m
                                return (True,b)
beta_reduce _                 = error "Lambda:beta_reduce"

{- mu reduction -}

mu_reduce :: Term -> VM (Bool,Term)
mu_reduce t@(Var v) = do
  c <- combinator v
  if isJust c
    then return $ (True,(\(Just x) -> x) c)
    else return $ (False,t)
mu_reduce _      = error "Lambda:mu_reduce"

eta_reduce :: Term -> (Bool,Term)
eta_reduce t@(Lam x (App m (Var y)))
    | x == y && (not $ elem y $ frees m) = (True,m)
    | otherwise                          = (False,t)
eta_reduce _                             = error "Lambda:eta_reduce"

{-----------------------------------------------------------------------}
{- functions to check whether a reduction was performed -}

recurse_check :: Bool -> Term -> Term -> Term
      -> (Term -> VM (Bool,Term))
      -> VM (Bool,Term)
recurse_check True ts _  n _ = return (True,App ts n)
recurse_check _    _  t1 n f = do
                               (red,ns) <- f n 
                               return (red,App t1 ns)

bet_check :: Term -> VM (Bool,Term)
bet_check t@(App    (Lam _ _) n) = beta_reduce t
bet_check (App t1@(Con _)   n) = do
  (bet_red,ns) <- bet_check n
  return $ (bet_red,App t1 ns)
bet_check (App t1@(Var _)   n) = do
  (bet_red,ns) <- bet_check n
  return $ (bet_red,App t1 ns)
bet_check t@(App t1@(App _ _) n) = do
  (bet_red,ts) <- bet_check t1
  recurse_check bet_red ts t1 n bet_check
bet_check t                      = return (False,t)

mu_check :: Term -> VM (Bool,Term)
mu_check t@(App t1@(Var _)   n) = do
  (mu_red,ts) <- mu_reduce t1
  recurse_check mu_red ts t1 n mu_check
mu_check t@(App t1@(App _ _) n) = do
  (mu_red,ts) <- mu_check t1
  recurse_check mu_red ts t1 n mu_check
mu_check t                      = return (False,t)

eta_check :: Term -> VM (Bool,Term)
eta_check t@(Lam _ (App _ (Var _))) = return $ eta_reduce t
eta_check t                         = return (False,t)

{-----------------------------------------------------------------------}
{- normal order evaluation (leftmost, outermost) -}

domap :: Constants -> Term -> Term
domap _ t@(Con _) = t
domap c t@(Var v)
  | M.member v c = Con v
  | otherwise    = t
domap c t@(Lam x m)
  | M.member x c = error "named constant as abstractor"
  | otherwise    = Lam x (domap c m)
domap c (App m n) = App (domap c m) (domap c n)

normal_order :: Term -> VM Term
--normal_order c t = let (_,ms) = eta_check c $ normal_order' c t
--in ms
normal_order t = do
  cs <- gets consts
  normal_order' (domap cs t)

normal_order' :: Term -> VM Term
normal_order' t@(Con _)   = return t
normal_order' t@(Var _)   = return t
normal_order' t@(Lam x m) = do
  n <- normal_order' m
  return $ Lam x n
normal_order' t@(App l m) = do
  (mu_red,ms) <- mu_check t
  if (mu_red) 
    then normal_order' ms  
    else do
         (bet_red,bs) <- bet_check t 
         if (bet_red)   
            then normal_order' bs
            else return bs

{-----------------------------------------------------------------------}
{- evaluation -}

eval :: Names -> Term -> Term
eval ns t = fst $ runVariableMonad (normal_order t) ns

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
_print' p   (Con n)                 = print_var p n
_print' p   (Var n)                 = print_var p n
_print' p t@(Lam _ _)               = print_lam p t
_print' p t@(App t1   t2@(App _ _)) = _print' p t1 ++ sp p ++ print_bra (_print' p t2) 
_print' p t@(App t1   t2@(Con _))   = _print'' p t1 ++ sp p ++ _print' p t2  
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

normal :: Names -> String -> String
normal ns = unparse . (eval ns) . parse

{-----------------------------------------------------------------------}
{- the main function -}

repl :: Names -> IO ()
repl n = do
  putStr "lambda term? "
  hFlush stdout
  input <- getLine
  case input of
       "quit" -> putStr "bye.\n"
       _      -> do putStr ("-> " ++ normal n input ++ "\n")
                    repl n 

main :: IO ()
main = do
  let ct = constants
      cb = M.map (domap ct . parse) combinators
  repl (ND cb ct fresh)

{-----------------------------------------------------------------------}

test1 = "^f x.f ((^x y.y) f x)"
test2 = parse test1
