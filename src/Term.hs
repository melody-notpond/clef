module Term
  ( Term (..)
  , Top (..)
  ) where
import Control.Monad.Trans.Reader

data Term =
    TUni Int
  | TGlobal String
  | TDeBruijn Int
  | TAnn Term Term
  | TPi (Maybe String) Term Term
  | TLam String (Maybe Term) Term
  | TApp Term Term
  deriving Eq

data Top =
    TAssign String Term
  | TTyping String Term

type PrettyM = Reader [String]

paren :: Int -> Int -> PrettyM String -> PrettyM String
paren current wanted p =
  do
    pretty <- p
    if current > wanted then
      return ("(" ++ pretty ++ ")")
    else return pretty

(!?) :: [a] -> Int -> Maybe a
[] !? _ = Nothing
(x:xs) !? n = if n == 0 then Just x else xs !? (n - 1)

prettyTerm' :: Int -> Term -> PrettyM String
prettyTerm' _ (TUni u) = return $ "𝕌#" ++ show u
prettyTerm' _ (TGlobal x) = return x
prettyTerm' _ (TDeBruijn n) =
  do
    g <- ask
    case g !? n of
      Just x -> return $ "#" ++ x
      Nothing -> return $ "#" ++ show n
prettyTerm' l (TAnn e t) = paren l 0 $ do
  e' <- prettyTerm' 1 e
  t' <- prettyTerm' 1 t
  return $ e' ++ ": " ++ t'
prettyTerm' l (TPi Nothing a r) = paren l 1 $ do
  a' <- prettyTerm' 2 a
  r' <- prettyTerm' 1 r
  return $ a' ++ " -> " ++ r'
prettyTerm' l (TPi (Just x) a r) = paren l 1 $ do
  a' <- prettyTerm' 1 a
  r' <- local (x:) (prettyTerm' 1 r)
  return $ "∀(" ++ x ++ ": " ++ a' ++ "), " ++ r'
prettyTerm' l (TLam x Nothing e) = paren l 2 $ do
  e' <- local (x:) (prettyTerm' 2 e)
  return $ "λ" ++ x ++ "." ++ e'
prettyTerm' l (TLam x (Just t) e) = paren l 2 $ do
  t' <- prettyTerm' 1 t
  e' <- local (x:) (prettyTerm' 2 e)
  return $ "λ(" ++ x ++ ": " ++ t' ++ "." ++ e'
prettyTerm' l (TApp f a) = paren l 3 $ do
  f' <- prettyTerm' 3 f
  a' <- prettyTerm' 4 a
  return $ f' ++ " " ++ a'

instance Show Term where
  show t = runReader (prettyTerm' 0 t) []

instance Show Top where
  show (TAssign x e) =
    "let " ++ x ++ " = " ++ show e
  show (TTyping x t) = "val " ++ x ++ " : " ++ show t
