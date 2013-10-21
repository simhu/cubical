module Core (Ter(..), fromProgram, removeNames) where

import Control.Monad.Reader hiding (ap)
import Data.Graph
import Data.List (elemIndex)

import qualified Program as P

-- The core language:
data Ter = Var Int
         | N | Z | S Ter | Rec Ter Ter Ter
         | Id Ter Ter Ter | Refl Ter
         | Trans Ter Ter Ter  -- Trans type eqprof proof
         | Pi Ter Ter | Lam Ter | App Ter Ter
         | Sigma Ter Ter | Pair Ter Ter | P Ter | Q Ter
  deriving Eq

-- Show instance for terms which insert names instead of De Bruijn indices
instance Show Ter where
  show e = runReader (show' e) ([],0)
    where
    show' (Var x)      = do
      (e,_) <- ask
      return (e !! x)
    show' N       = return "N"
    show' Z       = return "Z" -- 0?
    show' (S t)   = liftM (\x -> "S (" ++ x ++ ")") (show' t)
    show' (Rec t1 t2 t3) =
      liftM3 (\x y z -> "rec (" ++ x ++ ") (" ++ y ++ ") (" ++ z ++ ")")
             (show' t1) (show' t2) (show' t3)
    show' (Lam e) =  do
      (env,i) <- ask
      let x = vars !! i
      t <- local (\(e,i) -> (x : e, i+1)) (show' e)
      return $ "\\" ++ x ++ "." ++ t
    show' (App (App e1 e2) e3) =
      liftM3 (\x y z -> "(" ++ x ++ " " ++ y ++ ") " ++ z) (show' e1) (show' e2) (show' e3)
    show' (App e1 e2)  = liftM2 (\x y -> x ++ " " ++ y) (show' e1) (show' e2)

    vars = ["x","y","z"] ++ [ 'x' : show i | i <- [0..]]

-- Take a program, construct a call-graph and then compute the strongly
-- connected components. These correspond to the mutually recursive functions.
-- For now we forget these as recursion is not supported. This topologically
-- sorts the input functions which makes it possible to call constants defined
-- later in the file.
fromProgram :: P.Program -> Either String [(String,Ter)]
fromProgram p = liftM (zip ns) $ sequence [ removeNames ns t | (n,t) <- ts ]
  where -- Turn "f x y z = t" into "f = \x y z. t"
        p' = map (\(n,as,e) -> (n,P.Lam as e)) p
        -- Topologically sort
        ts = concatMap flattenSCC $ stronglyConnComp $ mkGraph p'
        ns = map fst ts

-- Construct the call-graph. For example if f contain a call to g then there
-- will be an arc from f to g.
mkGraph :: [(String,P.Expr)] -> [((String,P.Expr),String,[String])]
mkGraph p = [ ((n,e),n,P.freeVars e) | (n,e) <- p ]

-- Convert a lambda term to an anonymous lambda term.
removeNames :: [String] -> P.Expr -> Either String Ter
removeNames ctx (P.Lam [x] t)    = liftM Lam $ removeNames (x:ctx) t
removeNames ctx (P.Lam xs t)     = removeNames ctx (foldr (\x -> P.Lam [x]) t xs)
removeNames ctx (P.Var v)        = case elemIndex v ctx of
  Just index -> Right $ Var $ fromIntegral index
  Nothing    -> Left $ "Free variable: " ++ show v
removeNames ctx (P.App t1 t2)    = liftM2 App (removeNames ctx t1) (removeNames ctx t2)
removeNames _    P.N             = Right N
removeNames _    P.Z             = Right Z
removeNames ctx (P.S e)          = liftM S (removeNames ctx e)
removeNames ctx (P.Rec e1 e2 e3) =
  liftM3 Rec (removeNames ctx e1) (removeNames ctx e2) (removeNames ctx e3)
