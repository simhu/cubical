module InterMTT3 where

import MTT3
import Debug.Trace

type Name = String

data CExp =
   ELam Name CExp
 | ESet
 | EPi Name CExp CExp
 | ECon Name [CExp]
 | ESum [Label]
 | EFun [Branch]
 | EFst CExp
 | ESnd CExp
 | EApp CExp CExp
 | EVar Name
 | EDec Decl CExp
 | ETop
  deriving (Eq,Ord,Show)

data Decl =
   Dnotrec Patt Tel [CExp] 
 | Drec Patt Tel [CExp] 
  deriving (Eq,Ord,Show)

data Tel = Empty | Unit CExp | Sig Name CExp Tel
  deriving (Eq,Ord,Show)

type Patt = [Name]

type Branch = (Name,[Name],CExp)

type Label = (Name,Tel)

trads ps = map (trad ps)

trad :: [Name] -> CExp -> Exp

trad ps e0 = 
 case e0 of
  ELam p e -> Lam (trad (p:ps) e)
  ESet -> U
  ETop -> Top
  EPi p a b -> Pi (trad ps a) (Lam (trad (p:ps) b))
  EApp e1 e2 -> App (trad ps e1) (trad ps e2)
  ECon c es -> Con c (trads ps es)
  EFun bs -> Fun (map (tradFun ps) bs)
  ESum bs -> Sum (map (tradSum ps) bs)
  EVar n -> Ref (getV ps n)
  EDec d e -> tradDec ps d e

  where
    tradFun ps (c,p,e) = (c,trad (p ++ ps) e)


    tradSum ps (c,t) = (c,tradTel ps t)

    tradTel ps Empty = []
    tradTel ps (Unit a) = [trad ps a]
    tradTel ps (Sig x a t) = (trad ps a):(tradTel (x:ps) t)

    tradDec ps (Dnotrec p a e) e1 = Def (trad (p++ps) e1) (trads (p++ps) e) (tradTel ps a)
    tradDec ps (Drec p a e) e1 =  Def (trad (p++ps) e1) (trads (p++ps) e) (tradTel ps a)

getV [] n = error ("getV " ++ n ++ " is not declared")
getV (p:ps) n | n == p = 0
getV (p:ps) n          = 1 + (getV ps n)

------------------------------------------------------
-- Parsing functions
------------------------------------------------------


-- a simpl lexical analyser

data TOKEN = Iden String | Symbol String
  deriving (Eq,Show)

showTOKEN (Iden s) = "Iden " ++ s
showTOKEN (Symbol s) = "Symbol " ++ s

string_of_token :: TOKEN -> String
string_of_token (Iden s) = s
string_of_token (Symbol s) = s

sym :: String -> TOKEN
sym = Symbol

layout :: Char -> Bool
layout x = elem x "\n \t@" || x == '!' 

keyword :: String -> Bool

keyword x = 
 elem x ["let","letrec","data","fun","Top","Type","PN","Pi","Sig","One"]

symbolchar :: Char -> Bool
symbolchar x = elem x "#*:,|{}[]()=.\\%@;$."

keycheck :: String -> TOKEN
keycheck s = if keyword s then Symbol s else Iden s

myLex :: String -> [TOKEN]
myLex [] = [sym"EOT"]
myLex ('-':('>':rest)) = (sym"->"):(myLex rest)
myLex ('=':('=':rest)) = (sym"=="):(myLex rest)
myLex (':':(':':rest)) = (sym"::"):(myLex rest)
myLex ('{':('-':rest)) = getcomment rest
myLex ('"':rest) = getstring [] rest
myLex (a:rest) | layout a = myLex rest
                 | symbolchar a = (sym [a]):(myLex rest)
                 | otherwise = getword [a] rest

getcomment :: String -> [TOKEN]
getcomment [] = [sym"EOT"]
getcomment ('-':('}':rest)) = myLex rest
getcomment (a:rest) = getcomment rest

ismyAlphanum :: Char -> Bool
ismyAlphanum x = True -- isAlphaNum x || x == '_' 

getword s [] = [keycheck s,sym"EOT"]
getword s (l@(x:rest)) | layout x = (keycheck s):(myLex rest)
                       | symbolchar x = (keycheck s):(myLex l)
                       | ismyAlphanum x = getword (s++[x]) rest
                       | otherwise = (keycheck s):(myLex l)

getstring s [] = [sym"prim",Iden s,sym"EOT"]
getstring s ('"':rest) = sym"prim":((Iden s):(myLex rest))
getstring s (x:rest) = getstring (s++[x]) rest


type Parse a = [TOKEN] -> G (a,[TOKEN])

-- plus :: Parse a -> Parse [a]

plus f tkl =
 do
  (x,tkl1) <- f tkl
  case tkl1 of
    Symbol";":tkl2 -> 
       do
         (xs,tkl3) <- plus f tkl2
         return (x:xs,tkl3)
    _ -> return ([x],tkl1)

checkSymbol u (Symbol v:tkl) =
 if u == v 
    then return tkl
    else Fail ("checkSymbol, expected " ++ u ++ " but got " ++ v ++ show tkl)
checkSymbol u (Iden v:tkl) = Fail ("checkSymbol, expected " ++ u ++
                                      " but got " ++ v ++ show tkl)
checkSymbol u [] = Fail"checkSymbol"

parsePatt :: Parse Patt

parsePatt (Iden x:tkl) = 
 trace ("parsing " ++ x) (return ([x],tkl))
parsePatt  (Symbol"(":(Symbol")":tkl)) =
 return ([],tkl)
parsePatt (Symbol"(":(Iden x:(Symbol",":tkl))) =
 do
  (p1,tkl1) <- parsePatt1 tkl
  tkl4 <-  checkSymbol ")" tkl1
  return (p1++[x],tkl4)
parsePatt (u:tkl) = Fail("parsePatt " ++ show u)

parsePatt1 (Iden x:(Symbol",":tkl)) =
 do
  (p1,tkl1) <- parsePatt1 tkl
  return (p1++[x],tkl1)
parsePatt1 (Iden x:tkl) = 
 return ([x],tkl)
parsePatt1 _ = Fail"parsePatt1"
		
parseCExps :: Parse [CExp]

parseCExps  (Symbol"(":(Symbol")":tkl)) =
 return ([],tkl)
parseCExps (Symbol"(":tkl) =
 do
  (e,tkl1) <- parseCExp tkl
  tkl2 <-  checkSymbol "," tkl1
  (es,tkl3) <- parseCExps1 tkl2
  return (e:es,tkl3)
parseCExps tkl =
 do
  (e,tkl1) <- parseCExp tkl
  return ([e],tkl1)

parseCExps1 tkl =
 do
  (e,tkl1) <- parseCExp tkl
  case tkl1 of
   (Symbol")"):tkl2 -> return ([e],tkl2)
   (Symbol","):tkl2 -> 
    do
     (es,tkl3) <- parseCExps1 tkl2
     return (e:es,tkl3)

parseTel  (Symbol"(":(Symbol")":tkl)) = 
 return (Empty,tkl)
parseTel  (Symbol"(":(Iden x:(Symbol":":tkl))) = 
 do
  (a,tkl1) <- parseCExp tkl
  tkl2 <- checkSymbol "," tkl1
  (t,tkl3) <- parseTel1 tkl2
  return (Sig x a t,tkl3)
parseTel  tkl = 
 do
  (a,tkl1) <- parseCExp tkl
  return (Unit a,tkl1)

parseTel1 (Iden x:(Symbol":":tkl)) =
 do
  (a,tkl1) <- parseCExp tkl
  tkl2 <- checkSymbol "," tkl1
  (t,tkl3) <- parseTel1 tkl2
  return (Sig x a t,tkl3)
parseTel1 tkl = 
 do 
  (a,tkl1) <- parseCExp tkl
  tkl2 <- checkSymbol ")" tkl1
  return (Unit a,tkl2)

-- parseCExp2  :: CExp -> Parse CExp
-- parseCExp1  :: Parse CExp
-- parseCExp :: Parse CExp

arrow a b = EPi "" a b

parseCExp2  e tkl =
 case tkl of
    Iden u:_ ->
       do
        (b,tkl1) <- parseCExp1  tkl
        parseCExp2  (EApp e b) tkl1
    Symbol"(":tkl2 ->
       do
        (u,tkl3) <- parseCExp tkl2
        tkl4 <- checkSymbol ")" tkl3
        parseCExp2 (EApp e u) tkl4
    Symbol"->":tkl2 ->
       do
        (u,tkl3) <- parseCExp tkl2
        parseCExp2  (arrow e u) tkl3
    _ -> return (e,tkl) 

parseCExp tkl =
 do 
  (u,tkl1) <- parseCExp1 tkl
  parseCExp2  u tkl1

parseIden (Iden x:tkl) = return (x,tkl)
parseIden tkl = Fail "parseIden"

parseCExp1 (Symbol"(":(Symbol"Pi":tkl)) =
 do 
  (p,tkl1) <- parseIden tkl
  tkl2 <- checkSymbol ":" tkl1
  (a,tkl3) <- parseCExp tkl2
  tkl4 <- checkSymbol ")" tkl3
  (b,tkl5) <- parseCExp tkl4
  return (EPi p a b,tkl5)
parseCExp1 (Symbol"\\":tkl) = 
 do
  (p,tkl1) <- parseIden tkl
  tkl2 <- checkSymbol "->" tkl1
  (e,tkl5) <- parseCExp tkl2
  return (ELam p e,tkl5)
parseCExp1 (Symbol"fun":tkl1) =
 do
  tkl2 <- checkSymbol "[" tkl1
  (ces,tkl3) <- parseFun tkl2
  return (EFun ces,tkl3)
parseCExp1 (Symbol"data":(Symbol"(":tkl)) =
 do
  (ces,tkl1) <- parseSum tkl
  return (ESum ces,tkl1)
parseCExp1 (Symbol"(":tkl) =
 do
  (e,tkl1) <- parseCExp tkl
  tkl2 <- checkSymbol ")" tkl1
  return (e,tkl2)
parseCExp1 (Iden x:tkl1) =
 return (EVar x,tkl1)
parseCExp1 (Symbol"Type":tkl) =
 return (ESet,tkl)
parseCExp1 (Symbol"Top":tkl) =
 return (ETop,tkl)
parseCExp1 (Symbol"$":(Iden c:tkl)) =
 do
  (es,tkl1) <- parseCExps tkl
  return (ECon c es,tkl1)
parseCExp1 (Symbol"let":tkl) =
 do
  (p,tkl1) <- parsePatt tkl
  tkl2 <- checkSymbol ":" tkl1
  (a,tkl3) <- parseTel tkl2
  tkl4 <- checkSymbol "=" tkl3
  (e1,tkl5) <- parseCExps tkl4
  tkl6 <- checkSymbol ";" tkl5
  (e2,tkl7) <- parseCExp tkl6
  return (EDec (Dnotrec p a e1) e2,tkl7)
parseCExp1 (Symbol"letrec":tkl) =
 do
  (p,tkl1) <- parsePatt tkl
  tkl2 <- checkSymbol ":" tkl1
  (a,tkl3) <- parseTel tkl2
  tkl4 <- checkSymbol "=" tkl3
  (e1,tkl5) <- parseCExps tkl4
  tkl6 <- checkSymbol ";" tkl5
  (e2,tkl7) <- parseCExp tkl6
  return (EDec (Drec p a e1) e2,tkl7)
parseCExp1 tkl = Fail ("parseCExp1" ++ show tkl)

parseFun (Symbol"]":tkl) =
 return ([],tkl)
parseFun (Iden c:tkl) = 
 do
  (p,tkl1) <- parsePatt tkl
  tkl2 <- checkSymbol "->" tkl1
  (e,tkl3) <- parseCExp tkl2
  case tkl3 of
   (Symbol"]":tkl4) -> return ([(c,p,e)],tkl4)
   (Symbol"|":tkl4) ->
    do
     (ces,tkl5) <- parseFun tkl4
     return ((c,p,e):ces,tkl5)
parseFun tkl = Fail ("parseFun " ++ show tkl)

parseSum (Symbol")":tkl) =
 return ([],tkl)
parseSum (Iden c:(Symbol")":tkl)) =
 return ([(c, Empty)],tkl)
parseSum (Iden c:(Symbol"|":tkl)) = 
    do
     (ces,tkl5) <- parseSum tkl
     return ((c,Empty):ces,tkl5)
parseSum (Iden c:tkl) = 
 do
  (e,tkl1) <- parseTel  tkl
  case tkl1 of
   (Symbol")":tkl4) -> return ([(c,e)],tkl4)
   (Symbol"|":tkl4) ->
    do
     (ces,tkl5) <- parseSum tkl4
     return ((c,e):ces,tkl5)

------------------------------------------------------
-- Main checking routines
------------------------------------------------------

-- The input is checked as an expression of type One.
checkMain :: CExp -> G ()
checkMain e = check 0 Nil [] Top (trad [] e)

-- checking a string input
checkStr :: String -> IO()
checkStr s =
  case parseCExp $ myLex s of -- parsing using routines 
    Fail msg -> putStrLn $ "Parse error: " ++ msg
    Success  (e,_)  -> 
      case checkMain e of
        Fail  msg' -> putStrLn (show (trad [] e) ++ " type-checking failed:\n" ++ msg')
        Success _    -> putStrLn ("type-checking succeded.")

-- checking the content of a file.
checkFile :: String -> IO()
checkFile file = checkStr =<< readFile file
