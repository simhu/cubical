module Parser (Parser.parse, term) where

import Control.Applicative hiding ((<|>))
import Text.ParserCombinators.Parsec as P
import Text.ParserCombinators.Parsec.Token

import Program

tok :: TokenParser st
tok = makeTokenParser LanguageDef
  { commentStart    = "{-"
  , commentEnd      = "-}"
  , commentLine     = "--"
  , nestedComments  = True
  , identStart      = letter <|> char '_'
  , identLetter     = letter <|> digit <|> char '_'
  , opStart         = oneOf "\\=.;"
  , opLetter        = oneOf "\\=.;"
  , reservedNames   = ["Nat", "0", "succ", "rec"]
  , reservedOpNames = ["\\", ".", "=", ";"]
  , caseSensitive   = True
  }

parse :: String -> Either String Program
parse s = case P.parse program "" s of
  Left err -> Left (show err)
  Right x  -> Right x

program :: Parser Program
program = do
  ps <- P.many expr
  eof
  return ps

expr :: Parser (String,Args,Expr)
expr = do
  name <- identifier tok
  args <- P.many (identifier tok)
  reservedOp tok "="
  e    <- term
  reservedOp tok ";"
  return (name,args,e)

term :: Parser Expr
term = lambda <|> chainl1 atom (spaces >> return App)

lambda :: Parser Expr
lambda = do
  reservedOp tok "\\"
  xs <- many1 (identifier tok)
  reservedOp tok "."
  e <- term
  return $ Lam xs e

atom :: Parser Expr
atom =  Var <$> identifier tok
    <|> (reserved tok "Nat" >> return N)
    <|> (reserved tok "0"   >> return Z)
    <|> (reserved tok "succ" >> S <$> atom)
    <|> rec
    <|> parens tok term

-- Does this make sense?
rec :: Parser Expr
rec = do
  reserved tok "rec"
  e1 <- atom
  e2 <- atom
  e3 <- atom
  return $ Rec e1 e2 e3
