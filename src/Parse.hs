module Parse (parse) where

import Term
import Text.Megaparsec
  ( Parsec
  , (<?>)
  , optional
  , many
  , try
  , choice
  , between
  , runParser
  , eof )
import qualified Text.Megaparsec.Char.Lexer as L
import Text.Megaparsec.Char (space1, string, char, alphaNumChar)
import Control.Applicative ((<|>))
import Data.Functor (($>))
import Text.Megaparsec.Error (errorBundlePretty)
import Data.List (elemIndex)
import Data.Void (Void)
import Control.Monad.Trans.Reader

type Parser = ReaderT [String] (Parsec Void String)

sc :: Parser ()
sc = L.space
  space1
  (L.skipLineComment "--")
  (L.skipBlockCommentNested "{-" "-}")

lexeme :: Parser a -> Parser a
lexeme = L.lexeme sc

symbol :: String -> Parser String
symbol = L.symbol sc

-- LEXEMES

lexDot :: Parser ()
lexDot = symbol "." $> () <?> "dot"

lexComma :: Parser ()
lexComma = symbol "," $> () <?> "comma"

lexColon :: Parser ()
lexColon = symbol ":" $> () <?> "colon"

lexEqualsP :: Parser ()
lexEqualsP = symbol "=(" $> () <?> "equals paren"

lexEquals :: Parser ()
lexEquals = symbol "=" $> () <?> "equals"

lexDef :: Parser ()
lexDef = symbol ":=" $> () <?> "define"

lexLParen :: Parser ()
lexLParen = symbol "(" $> () <?> "left paren"

lexRParen :: Parser ()
lexRParen = symbol ")" $> () <?> "right paren"

lexLArrow :: Parser ()
lexLArrow = symbol "->" $> () <?> "left arrow"

lexLam :: Parser ()
lexLam = (symbol "\\" <|> symbol "λ") $> () <?> "lambda symbol"

lexForall :: Parser ()
lexForall =
  (symbol "∀" <|> symbol "forall" <|> symbol "pi" <|> symbol "Π") $> ()
  <?> "for all symbol"

lexLet :: Parser ()
lexLet = symbol "let" $> () <?> "let"

lexVal :: Parser ()
lexVal = symbol "val" $> () <?> "val"

lexRefl :: Parser ()
lexRefl = symbol "refl" $> () <?> "refl"

lexVar :: Parser String
lexVar = lexeme
  (do
    x <- char '\'' <|> alphaNumChar
    xs <- many (char '\'' <|> alphaNumChar)
    let s = x:xs
    if (s == "forall") ||
      (s == "pi") ||
      (s == "val") ||
      (s == "let") ||
      (s == "refl") ||
      (s == "Uni")
    then
      fail "invalid symbol"
    else return s) <?> "variable token"

-- PARSERS

var :: Parser Term
var =
  do
    v <- lexVar
    g <- ask
    return $ case elemIndex v g of
      Just i -> TDeBruijn i
      Nothing -> TGlobal v

uni :: Parser Term
uni = lexeme
  (do
    (string "Uni" <|> string "𝕌") $> ()
    TUni <$> try (char '#' >> L.decimal))
  <?> "universe"

value :: Parser Term
value = choice [
    try var
  , try uni
  , between lexLParen lexRParen ann]
  <?> "value"

ann :: Parser Term
ann =
  do
    e <- choice [try piType, try equals, try lambda, app]
    t <- optional (lexColon >> choice [try piType, try equals, try lambda, app])
    case t of
      Just t' -> return (TAnn e t') <?> "type annotation"
      Nothing -> return e

func :: Parser Term
func =
  do
    a <- choice [try equals, try lambda, app]
    lexLArrow
    r <- choice [try piType, try equals, try lambda, app]
    return (TPi Nothing a r)

forAll :: Parser Term
forAll =
  do
    lexForall
    lexLParen
    x <- lexVar
    lexColon
    t <- choice [try piType, try equals, try lambda, app]
    lexRParen
    lexComma
    p <- local (x:) (choice [try piType, try equals, try lambda, app])
    return (TPi (Just x) t p)

piType :: Parser Term
piType = (try func <|> forAll) <?> "function/pi type"

equals :: Parser Term
equals =
  do
    a <- choice [try lambda, app]
    t <- choice [try
      (lexEqualsP >> do t <- term; lexRParen; return $ Just t),
      lexEquals >> return Nothing]
    b <- choice [try lambda, app]
    return $ TEq t a b

lambdaBinding :: Parser (String, Maybe Term)
lambdaBinding =
  do
    lexLParen
    x <- lexVar
    lexColon
    t <- choice [try piType, try lambda, app]
    lexRParen
    return (x, Just t)

lambda :: Parser Term
lambda =
  (do
    lexLam
    (x, t) <- (lambdaBinding <|> (lexVar >>= \x -> return (x, Nothing)))
      <?> "lambda binding"
    lexDot
    e <- local (x:) (choice [try lambda, app])
    return (TLam x t e)) <?> "lambda"

app :: Parser Term
app =
  try (do
    f <- value
    xs <- many value
    return $ foldl TApp f xs) <|>
  (do
    lexRefl
    TRefl <$> value) <?> "application"

term :: Parser Term
term = ann <?> "term"

assign :: Parser Top
assign =
  (do
    lexLet
    f <- lexVar
    args <- many lexVar
    lexDef
    t <- local (reverse args++) term
    let t' = foldr (`TLam` Nothing) t args
    return $ TAssign f t') <?> "assignment"

typing :: Parser Top
typing =
  (do
    lexVal
    f <- lexVar
    lexColon
    TTyping f <$> term) <?> "typing"

top :: Parser [Top]
top =
  do
    sc
    ts <- many $ try typing <|> assign
    eof
    return ts

parse :: String -> String -> Either String [Top]
parse name contents =
  case runParser (runReaderT top []) name contents of
    Left e -> Left $ errorBundlePretty e
    Right v -> Right v
