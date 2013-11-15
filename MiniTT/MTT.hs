-- nameless miniTT, with recursive definitions
module MiniTT.MTT where

import Control.Monad
import Debug.Trace
import Control.Monad.Error hiding (Error,fix)

type Brc = [(String,Exp)]
type Lb  = [(String,[Exp])]

data Exp = Comp Exp Env
         | App Exp Exp
         | Pi Exp Exp
         | Lam Exp
           -- TODO: Should be a list of pairs!
         | Def Exp [Exp] [Exp]	-- unit substitutions
         | Var Int 		-- generic values
         | Ref Int		-- de Bruijn index
         | U
         | Con String [Exp]
         | Fun Brc
         | Sum Lb
         | PN String Exp        -- primitive notion (typed)
         | Top
  deriving (Eq,Show)

data Env = Empty
         | Pair Env Exp
         | PDef [Exp] [Exp] Env
  deriving (Eq,Show)

upds :: Env -> [Exp] -> Env
upds = foldl Pair

eval :: Exp -> Env -> Exp       -- eval is also composition!
eval (Def e es as) s = eval e (PDef es as s)
eval (App t1 t2)   s = app (eval t1 s) (eval t2 s)
eval (Pi a b)      s = Pi (eval a s) (eval b s)
eval (Con c ts)    s = Con c (evals ts s)
eval (Ref k)       s = getE k s
eval U             _ = U
eval (PN n a)      s = PN n (eval a s)
eval t             s = Comp t s

evals :: [Exp] -> Env -> [Exp]
evals es r = map (\e -> eval e r) es

app :: Exp -> Exp -> Exp
app (Comp (Lam b) s)     u            = eval b (Pair s u)
app a@(Comp (Fun ces) r) b@(Con c us) = case lookup c ces of
  Just e  -> eval e (upds r us)
  Nothing -> error $ "app: " ++ show a ++ " " ++ show b
app f                    u            = App f u

getE :: Int -> Env -> Exp
getE 0 (Pair _ u)       = u
getE k (Pair s _)       = getE (pred k) s
getE l r@(PDef es _ r1) = getE l (upds r1 (evals es r))

addC :: [Exp] -> [Exp] -> Env -> [Exp] -> [Exp]
addC gam _      _  []     = gam
addC gam (a:as) nu (u:us) = addC (eval a nu:gam) as (Pair nu u) us

-- An error monad
type Error a = Either String a

(=?=) :: Error Exp -> Exp -> Error ()
m =?= s2 = do
  s1 <- m
  unless (s1 == s2) $ Left ("eqG " ++ show s1 ++ " =/= " ++ show s2)

checkD :: Int -> Env -> [Exp] -> [Exp] -> [Exp] -> Error ()
checkD k rho gam es as = do
  (rho1,gam1,l) <- checkTs k rho gam as
  checks l rho1 gam1 as rho es

checkTs :: Int -> Env -> [Exp] -> [Exp] -> Error (Env,[Exp],Int)
checkTs k rho gam []     = return (rho,gam,k)
checkTs k rho gam (a:as) = do
  checkT k rho gam a
  checkTs (k+1) (Pair rho (Var k)) (eval a rho:gam) as

checkT :: Int -> Env -> [Exp] -> Exp -> Error ()
checkT k rho gam t = case t of
  U            -> return ()
  Pi a (Lam b) -> do
    checkT k rho gam a
    checkT (k+1) (Pair rho (Var k)) (eval a rho:gam) b
  _ -> checkI k rho gam t =?= U

check :: Int -> Env -> [Exp] -> Exp -> Exp -> Error ()
check k rho gam a t = case (a,t) of
  (Top,Top)    -> return ()
  (_,Con c es) -> do
    (bs,nu) <- extSG c a
    checks k rho gam bs nu es
  (U,Pi a (Lam b)) -> do
    check k rho gam U a
    check (k+1) (Pair rho (Var k)) (eval a rho:gam) U b
  (U,Sum bs) -> sequence_ [checkTUs k rho gam as | (_,as) <- bs]
  (Pi (Comp (Sum cas) nu) f,Fun ces) ->
    if map fst ces == map fst cas
       then sequence_ [ fix k rho gam as nu f c e
                      | ((c,e), (_,as)) <- zip ces cas]
       else fail "case branches does not match the data type"
  (Pi a f,Lam t)  -> check (k+1) (Pair rho (Var k)) (a:gam) (app f (Var k)) t
  (_,Def e es as) -> do
    checkD k rho gam es as
    let rho1 = PDef es as rho
    check k rho1 (addC gam as rho (evals es rho1)) a e
  _ -> checkI k rho gam t =?= a

checkTUs :: Int -> Env -> [Exp] -> [Exp] -> Error ()
checkTUs _ _   _   []     = return ()
checkTUs k rho gam (a:as) = do
  check k rho gam U a
  checkTUs (k+1) (Pair rho (Var k)) (eval a rho:gam) as

-- What does this do?
fix k rho gam as nu f c e = do
  let l  = length as
  let us = map Var [k..k+l-1]
  check (k+l) (upds rho us) (addC gam as nu us) (app f (Con c us)) e

extSG :: String -> Exp -> Error ([Exp], Env)
extSG c (Comp (Sum cas) r) = case lookup c cas of
  Just as -> return (as,r)
  Nothing -> Left ("extSG " ++ show c)
extSG c u = Left ("extSG " ++ c ++ " " ++ show u)

checkI :: Int -> Env -> [Exp] -> Exp -> Error Exp
checkI k rho gam e = case e of
  Ref k   -> return (gam !! k)
  App n m -> do
    c <- checkI k rho gam n
    case c of
      Pi a f -> do
        check k rho gam a m
        return (app f (eval m rho))
      _      ->  Left $ show c ++ " is not a product"
  Def t es as -> do
    checkD k rho gam es as
    let rho1 = PDef es as rho
    checkI k rho1 (addC gam as rho (evals es rho1)) t
  PN _ a -> return (eval a rho)
  _ -> Left ("checkI " ++ show e ++ " in " ++ show rho)


checks :: Int -> Env -> [Exp] -> [Exp] -> Env -> [Exp] -> Error ()
checks _ _   _    []    _  []     = return ()
checks k rho gam (a:as) nu (e:es) = do
  trace ("checking " ++ show e ++ " of type " ++ show a
         ++ " in " ++ show rho ++ "\n")
    (check k rho gam (eval a nu) e)
  checks k rho gam as (Pair nu (eval e rho)) es
checks k rho gam _ _ _ = Left "checks"


checkExp :: Exp -> Error ()
checkExp = check 0 Empty [] Top
