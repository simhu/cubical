module Core (Ter(..), fromProgram, removeNames) where

import Data.Graph
import Data.List (elemIndex)

import qualified Program as P

-- The core language:
data Ter = Var Int
         | N | Z | S Ter | Rec Ter Ter Ter
         | Id Ter Ter Ter | Refl Ter
         | Trans Ter Ter Ter  -- Trans type eqprof proof
         | Pi Ter Ter | Lam Ter | App Ter Ter
  deriving (Show, Eq)

-- Take a program, construct a call-graph and then compute the strongly 
-- connected components. These correspond to the mutually recursive functions.
fromProgram :: P.Program -> [[(String,Ter)]]
fromProgram = map flattenSCC         
            . stronglyConnComp 
            . mkGraph 
            . map (\(name,as,e) -> (name, removeNames (P.Lam as e)))

-- Construct the call-graph. For example if f contain a call to g then there 
-- will be an arc from f to g. 
mkGraph :: [(String,Ter)] -> [((String,Ter),String,[String])]
mkGraph [] = []
mkGraph ((n,e):xs) = ((n,e),n,allFree e) : mkGraph xs
  where
  allFree (Lam e)         = allFree e
  allFree (App e1 e2)     = allFree e1 ++ allFree e2
--  allFree (Free x)        = [x]
  allFree _               = []

-- Convert a lambda term to an anonymous lambda term and do the transformation:
-- \x y z. t  -> \x. \y. \z. t
removeNames :: P.Expr -> Ter
removeNames = removeNames' [] 
  where
  removeNames' :: [String] -> P.Expr -> Ter
  removeNames' ctx (P.Lam [x] t)    = Lam $ removeNames' (x:ctx) t
  removeNames' ctx (P.Lam xs t)     = removeNames' ctx (foldr (\x -> P.Lam [x]) t xs) 
  removeNames' ctx (P.Var v)        = case elemIndex v ctx of
        Just index -> Var $ fromIntegral index
        Nothing    -> error $ "removeNames: Free variable: " ++ show v -- Free v
  removeNames' ctx (P.App t1 t2)    = App (removeNames' ctx t1) (removeNames' ctx t2)  
  removeNames' _    P.N             = N
  removeNames' _    P.Z             = Z
  removeNames' ctx (P.S e)          = S (removeNames' ctx e)
  removeNames' ctx (P.Rec e1 e2 e3) = 
    Rec (removeNames' ctx e1) (removeNames' ctx e2) (removeNames' ctx e3)
