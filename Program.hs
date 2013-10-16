module Program (Program, Args, Expr(..), freeVars) where

import Data.List ((\\))

-- The non-core language:
type Program = [(String,Args,Expr)]
type Args    = [String]

-- What to do with Free variables?
data Expr = Lam [String] Expr
          | App Expr Expr
          | Var String
          | N
          | Z
          | S Expr
          | Rec Expr Expr Expr
-- ...      

freeVars :: Expr -> [String]
freeVars (Lam xs e)     = freeVars e \\ xs
freeVars (App e1 e2)    = freeVars e1 ++ freeVars e2
freeVars (Var x)        = [x]
freeVars (S e)          = freeVars e
freeVars (Rec e1 e2 e3) = freeVars e1 ++ freeVars e2 ++ freeVars e3
freeVars _              = []

-- TODO: Finish!
instance Show Expr where
  show (Lam xs t)              = "\\" ++ unwords xs ++ ". " ++ show t
  show (App (Var v1) (Var v2)) = v1 ++ " " ++ v2
  show (App (Var v) t2)        = v ++ " (" ++ show t2 ++ ")"
  show (App t1 (Var v))        = "(" ++ show t1 ++ ") " ++ v
  show (App t1 t2)             = "(" ++ show t1 ++ ") (" ++ show t2 ++ ")"
  show (Var v)                 = v


-- data Ter = Var Int
--          | N | Z | S Ter | Rec Ter Ter Ter
--          | Id Ter Ter Ter | Ref Ter
--          | Trans Ter Ter Ter  -- Trans type eqprof proof
--          | Pi Ter Ter | Lam Ter | App Ter Ter
--   deriving (Show, Eq)
