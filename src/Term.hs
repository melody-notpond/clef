module Term
  ( Term (..)
  , Top (..)
  , showWith
  ) where
import Control.Monad.Trans.Reader

data Term =
  -- universes
    TUni Int

  -- variables
  | TGlobal String
  | TDeBruijn Int

  -- assumed propositions
  | TAssumed

  -- annotations
  | TAnn Term Term

  -- pi type stuff
  | TPi (Maybe String) Term Term
  | TLam String (Maybe Term) Term
  | TApp Term Term

  -- equality type stuff
  | TEq (Maybe Term) Term Term
  | TRefl Term

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

prettyTerm :: Int -> Term -> PrettyM String
prettyTerm _ (TUni u) = return $ "𝕌#" ++ show u
prettyTerm _ TAssumed = return "ASSUMED"
prettyTerm _ (TGlobal x) = return x
prettyTerm _ (TDeBruijn n) =
  do
    g <- ask
    case g !? n of
      Just x -> return $ x ++ "#" ++ show n
      Nothing -> return $ "#" ++ show n
prettyTerm l (TAnn e t) = paren l 0 $ do
  e' <- prettyTerm 1 e
  t' <- prettyTerm 1 t
  return $ e' ++ ": " ++ t'
prettyTerm l (TPi Nothing a r) = paren l 1 $ do
  a' <- prettyTerm 2 a
  r' <- prettyTerm 1 r
  return $ a' ++ " -> " ++ r'
prettyTerm l (TPi (Just x) a r) = paren l 1 $ do
  a' <- prettyTerm 1 a
  r' <- local (x:) (prettyTerm 1 r)
  return $ "∀(" ++ x ++ ": " ++ a' ++ "), " ++ r'
prettyTerm l (TLam x Nothing e) = paren l 3 $ do
  e' <- local (x:) (prettyTerm 3 e)
  return $ "λ" ++ x ++ "." ++ e'
prettyTerm l (TLam x (Just t) e) = paren l 3 $ do
  t' <- prettyTerm 1 t
  e' <- local (x:) (prettyTerm 3 e)
  return $ "λ(" ++ x ++ ": " ++ t' ++ "." ++ e'
prettyTerm l (TApp f a) = paren l 4 $ do
  f' <- prettyTerm 4 f
  a' <- prettyTerm 5 a
  return $ f' ++ " " ++ a'
prettyTerm l (TEq Nothing a b) = paren l 2 $ do
  a' <- prettyTerm 3 a
  b' <- prettyTerm 3 b
  return $ a' ++ " = " ++ b'
prettyTerm l (TEq (Just t) a b) = paren l 2 $ do
  t' <- prettyTerm 1 t
  a' <- prettyTerm 3 a
  b' <- prettyTerm 3 b
  return $ a' ++ " =(" ++ t' ++ ") " ++ b'
prettyTerm l (TRefl a) = paren l 4 $ do
  a' <- prettyTerm 5 a
  return $ "refl " ++ a'

showWith :: Term -> [String] -> String
showWith t = runReader (prettyTerm 0 t) 

instance Show Term where
  show t = runReader (prettyTerm 0 t) []

instance Show Top where
  show (TAssign x e) =
    "let " ++ x ++ " = " ++ show e
  show (TTyping x t) = "val " ++ x ++ " : " ++ show t
