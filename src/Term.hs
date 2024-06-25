module Term (Term (..), prettyTerm, Top (..)) where

data Term =
    TUni (Maybe Int)
  | TVar String
  | TAnn Term Term
  | TPi (Maybe String) Term Term
  | TLam String (Maybe Term) Term
  | TApp Term Term

data Top =
    TAssign String [String] Term
  | TTyping String Term

paren :: Int -> Int -> String -> String
paren current wanted pretty =
  if current > wanted then
    "(" ++ pretty ++ ")"
  else pretty

prettyTerm' :: Int -> Term -> String
prettyTerm' _ (TUni Nothing) = "Uni"
prettyTerm' _ (TUni (Just u)) = "Uni#" ++ show u
prettyTerm' _ (TVar x) = x
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
