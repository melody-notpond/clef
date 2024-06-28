module Term
  ( Term (..)
  , Top (..)
  , prettyTerm
  , toDeBruijn
  , toDeBruijn'
  , fromDeBruijn
  , remAssignArgs
  ) where
import Data.List (elemIndex)

data Term =
    TUni (Maybe Int)
  | TVar String
  | TDeBruijn Int
  | TAnn Term Term
  | TPi (Maybe String) Term Term
  | TLam String (Maybe Term) Term
  | TApp Term Term
  deriving Eq

data Top =
    TAssign String [String] Term
  | TTyping String Term

paren :: Int -> Int -> String -> String
paren current wanted pretty =
  if current > wanted then
    "(" ++ pretty ++ ")"
  else pretty

prettyTerm' :: Int -> Term -> String
prettyTerm' _ (TUni Nothing) = "𝕌"
prettyTerm' _ (TUni (Just u)) = "𝕌#" ++ show u
prettyTerm' _ (TVar x) = x
prettyTerm' _ (TDeBruijn n) = "#" ++ show n
prettyTerm' l (TAnn e t) = paren l 0 $
  prettyTerm' 1 e ++ ": " ++ prettyTerm' 1 t
prettyTerm' l (TPi Nothing a r) = paren l 1 $
  prettyTerm' 2 a ++ " -> " ++ prettyTerm' 1 r
prettyTerm' l (TPi (Just x) a r) = paren l 1 $
  "∀(" ++ x ++ ": " ++ prettyTerm' 1 a ++ "), " ++ prettyTerm' 1 r
prettyTerm' l (TLam x Nothing e) = paren l 2 $
  "λ" ++ x ++ "." ++ prettyTerm' 2 e
prettyTerm' l (TLam x (Just t) e) = paren l 2 $
  "λ(" ++ x ++ ": " ++ prettyTerm' 1 t ++ "." ++ prettyTerm' 2 e
prettyTerm' l (TApp f a) = paren l 3 $
  prettyTerm' 3 f ++ " " ++ prettyTerm' 4 a

prettyTerm :: Term -> String
prettyTerm = prettyTerm' 0

instance Show Term where
  show = prettyTerm

instance Show Top where
  show (TAssign x args e) =
    "let " ++ x ++ foldl (\b a -> b ++ " " ++ a) "" args ++ " = " ++ show e
  show (TTyping x t) = "val " ++ x ++ " : " ++ show t

toDeBruijn' :: [String] -> Term -> Term
toDeBruijn' ctx (TVar x) =
  case elemIndex x ctx of
    Just i -> TDeBruijn i
    Nothing -> TVar x
toDeBruijn' ctx (TLam x t e) = TLam x t (toDeBruijn' (x:ctx) e)
toDeBruijn' ctx (TAnn e t) = TAnn (toDeBruijn' ctx e) (toDeBruijn' ctx t)
toDeBruijn' ctx (TPi (Just x) a r) =
    TPi (Just x) (toDeBruijn' ctx a) (toDeBruijn' (x:ctx) r)
toDeBruijn' ctx (TPi Nothing a r) =
  TPi Nothing (toDeBruijn' ctx a) (toDeBruijn' ctx r)
toDeBruijn' ctx (TApp f a) = TApp (toDeBruijn' ctx f) (toDeBruijn' ctx a)
toDeBruijn' _ t = t

toDeBruijn :: Term -> Term
toDeBruijn = toDeBruijn' []

fromDeBruijn :: [String] -> Term -> Term
fromDeBruijn ctx (TDeBruijn n) = TVar $ ctx !! n
fromDeBruijn ctx (TLam x t e) = TLam x t (fromDeBruijn (x:ctx) e)
fromDeBruijn ctx (TAnn e t) = TAnn (fromDeBruijn ctx e) (fromDeBruijn ctx t)
fromDeBruijn ctx (TPi (Just x) a r) =
  TPi (Just x) (fromDeBruijn ctx a) (fromDeBruijn (x:ctx) r)
fromDeBruijn ctx (TPi Nothing a r) =
  TPi Nothing (fromDeBruijn ctx a) (fromDeBruijn ctx r)
fromDeBruijn ctx (TApp f a) = TApp (fromDeBruijn ctx f) (fromDeBruijn ctx a)
fromDeBruijn _ t = t

remAssignArgs :: Top -> Top
remAssignArgs (TAssign f (x:xs) e) =
  remAssignArgs (TAssign f xs (TLam x Nothing e))
remAssignArgs t = t
