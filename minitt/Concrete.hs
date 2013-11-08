module Concrete where

import Control.Applicative hiding ((<|>),many)
import Text.ParserCombinators.Parsec as P
import Text.ParserCombinators.Parsec.Token

type Args = [Maybe String]
type Tele = [(Maybe String,Exp)]
type Rec  = Bool

data Exp = Lam Args Exp
         | App Exp Exp
         | Var String
         | Pi Tele Exp
         | Case Exp [(String,Args,Exp)]  -- TODO: Support _?
         | Con String [Exp]  
         | Let Rec [DefDecl] Exp
         | U  
  deriving (Eq,Show)           
           
data DefDecl =
  DefDecl { defName :: String
          , defType :: Exp
          , defArgs :: Args
          , defBody :: Exp
          }
  deriving (Eq,Show)
           
data DataDecl =
  DataDecl { dataName :: String
           , dataTele :: Tele
           , dataSum  :: [(String,Tele)]
           }
  deriving (Eq,Show)

type Program = [Either DefDecl DataDecl ]


tok :: TokenParser st
tok = makeTokenParser LanguageDef
  { commentStart    = "{-"
  , commentEnd      = "-}"
  , commentLine     = "--"
  , nestedComments  = True
  , identStart      = letter
  , identLetter     = alphaNum
  , opStart         = oneOf "\\=-:;|"
  , opLetter        = oneOf "\\=->:;|"
  , reservedNames   = ["U", "case", "of", "data", "let", "in", "_"]
  , reservedOpNames = ["\\", "->", "=", ";", ":"]
  , caseSensitive   = True
  }

parse :: String -> Either String Program
parse s = case P.parse program "" s of
  Left err -> Left (show err)
  Right x  -> Right x

program :: Parser Program
program = do
  ps <- P.many ((Left <$> defDecl) <|> (Right <$> dataDecl))
  eof
  return ps

defDecl :: Parser DefDecl
defDecl = do
  name  <- identifier tok
  reserved tok ":"
  dtype <- expr
  reserved tok ";"
--  newline
  -- n' <- identifier tok
  string name
  xs  <- args
  reserved tok "="
  exp <- expr
  reserved tok ";"
  return (DefDecl name dtype xs exp)

dataDecl :: Parser DataDecl
dataDecl = do
  reserved tok "data"
  name  <- identifier tok
--  reservedOp tok ":"
  dtele <- tele
  reservedOp tok "="
  dsum  <- sepBy (do s <- identifier tok
                     t <- tele
                     return (s,t))
                 (reserved tok "|")
  reserved tok ";"
  return (DataDecl name dtele dsum)

arg :: Parser (Maybe String)
arg =  (reserved tok "_" >> return Nothing)
   <|> (Just <$> identifier tok)

args :: Parser Args
args = many arg

varDecls :: Parser [(Maybe String,Exp)]
varDecls = do
  as <- sepBy1 arg spaces
  reserved tok ":"
  exp <- expr
  return (zip as (repeat exp))

tele :: Parser Tele
tele = do
  vds <- many (parens tok varDecls)
  return (concat vds)

expr :: Parser Exp
expr = lambda <|> chainl1 atom (spaces >> return App)

lambda :: Parser Exp
lambda = do
  reservedOp tok "\\"
  xs <- args
  reservedOp tok "->"
  e <- expr
  return $ Lam xs e

atom :: Parser Exp
atom =  Var <$> identifier tok
    <|> (reserved tok "U" >> return U) 
    <|> parens tok expr
