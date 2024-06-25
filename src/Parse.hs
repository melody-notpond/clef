module Parse (parse) where

import Term
import Data.Void (Void)
import Text.Megaparsec (Parsec, (<?>), optional, many, try, choice, notFollowedBy, between, runParser, eof)
import qualified Text.Megaparsec.Char.Lexer as L
import Text.Megaparsec.Char (space1, string, char, alphaNumChar)
import Control.Applicative ((<|>))
import Data.Functor (($>))
import Text.Megaparsec.Error (errorBundlePretty)

type Parser = Parsec Void String

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

lexEquals :: Parser ()
lexEquals = symbol "=" $> () <?> "equals"

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

lexVar :: Parser String
lexVar = lexeme
  (do
    notFollowedBy (lexForall <|> lexLet <|> lexVal)
    x <- char '\'' <|> alphaNumChar
    xs <- many (char '\'' <|> alphaNumChar)
    return (x:xs)) <?> "variable token"

-- PARSERS

var :: Parser Term
var = TVar <$> lexVar

uni :: Parser Term
uni = lexeme
  (do
    (string "Uni" <|> string "𝕌") $> ()
    level <- optional (try (char '#' >> L.decimal))
    return (TUni level))
  <?> "universe"

value :: Parser Term
value = choice [
    try uni
  , try var
  , between lexLParen lexRParen ann]
  <?> "value"

ann :: Parser Term
ann =
  do
    e <- choice [try piType, try lambda, app] 
    t <- optional (lexColon >> choice [try piType, try lambda, app])
    case t of
      Just t' -> return (TAnn e t') <?> "type annotation"
      Nothing -> return e

func :: Parser Term
func =
  do
    a <- choice [try lambda, app]
    lexLArrow
    r <- choice [try piType, try lambda, app]
    return (TPi Nothing a r)

forAll :: Parser Term
forAll =
  do
    lexForall
    lexLParen
    x <- lexVar
    lexColon
    t <- choice [try piType, try lambda, app]
    lexRParen
    lexComma
    p <- choice [try piType, try lambda, app]
    return (TPi (Just x) t p)

piType :: Parser Term
piType = (try func <|> forAll) <?> "function/pi type"

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
    e <- choice [try lambda, app]
    return (TLam x t e)) <?> "lambda"

app :: Parser Term
app =
  (do
    f <- value
    xs <- many value
    return $ foldl TApp f xs) <?> "application"

term :: Parser Term
term = ann <?> "term"

assign :: Parser Top
assign =
  (do
    lexLet
    f <- lexVar
    args <- many lexVar
    lexEquals
    TAssign f args <$> term) <?> "assignment"

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
  case runParser top name contents of
    Left e -> Left $ errorBundlePretty e
    Right v -> Right v
