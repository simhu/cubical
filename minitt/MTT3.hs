-- nameless miniTT, with recursive definitions

module MTT3 where

import Debug.Trace

type Brc = [(String,Exp)]

type Lb = [(String,[Exp])]

data Exp = 
   Comp Exp Env
 | App Exp Exp
 | Pi Exp Exp
 | Lam Exp
 | Def Exp [Exp] [Exp]	-- unit substitutions
 | Var Int 		-- generic values
 | Ref Int		-- de Bruijn index
 | U
 | Con String [Exp]
 | Fun Brc
 | Sum Lb
 | Top
	deriving (Show,Eq)
 
data Env = Nil | Pair Env Exp | PDef [Exp] [Exp] Env
	deriving (Show,Eq)

upds r [] = r
upds r (u:us) = upds (Pair r u) us

eval :: Exp -> Env -> Exp       -- eval is also composition!
eval (Def e es as) s = eval e (PDef es as s)
eval (App t1 t2) s = app (eval t1 s) (eval t2 s)
eval (Pi a b) s = Pi (eval a s) (eval b s)
eval (Con c ts) s = Con c (evals ts s)
eval (Ref k) s = getE k s
eval U s = U
eval t s = Comp t s

evals [] r = []
evals (e:es) r = (eval e r):(evals es r)

app :: Exp -> Exp -> Exp
app (Comp (Lam b) s) u = eval b (Pair s u)
app (Comp (Fun ces) r) (Con c us) = eval (get c ces) (upds r us)
app f u = App f u

getE 0 (Pair _ u) = u
getE k (Pair s _) = getE (pred k) s -- was written with k+1 pattern, not ok anymore
getE l r@(PDef es _ r1) = getE l (upds r1 (evals es r))

data G a = Success a | Fail String

instance  Monad G  where
    (Success x) >>= k     =  k x
    Fail s   >>= k   =  Fail s
    return           =  Success
    fail             =  Fail

eqG s1 s2 | s1 == s2 = return ()
eqG s1 s2            = Fail ("eqG " ++ show s1 ++ " =/= " ++ show s2) 

check :: Int -> Env -> [Exp] -> Exp -> Exp -> G ()
checkT :: Int -> Env -> [Exp] -> Exp -> G ()
checkI :: Int -> Env -> [Exp] -> Exp -> G Exp
checkD :: Int -> Env -> [Exp] -> [Exp] -> [Exp] -> G ()

checkTs :: Int -> Env -> [Exp] -> [Exp] -> G (Env,[Exp],Int)

checkTs k rho gam [] = return (rho,gam,k)
checkTs k rho gam (a:as) =
 do
  checkT k rho gam a
  checkTs (k+1) (Pair rho (Var k)) ((eval a rho):gam) as

checkTUs k rho gam [] = return ()
checkTUs k rho gam (a:as) =
 do
  check k rho gam U a
  checkTUs (k+1) (Pair rho (Var k)) ((eval a rho):gam) as

checkD k rho gam es as =
 do
  (rho1,gam1,l) <- checkTs k rho gam as
  checks l rho1 gam1 as rho es

checkT k rho gam t = case t of
 U -> return ()
 Pi a (Lam b) -> do
                   checkT k rho gam a
                   checkT (k+1) (Pair rho (Var k)) ((eval a rho):gam) b
 _ -> do
       a <- checkI k rho gam t
       eqG U a

fix k rho gam as nu f c e =
 do
  let l = length as
  let us = vars k l
  check (k+l) (upds rho us) (addC gam as nu us) (app f (Con c us)) e

check k rho gam a t = case (a,t) of
 (Top,Top) -> return ()
 (_,Con c es) -> do
                 (bs,nu) <- extSG c a
                 checks k rho gam bs nu es
 (U,Pi a (Lam b)) -> do
       	      	      check k rho gam U a
		      check (k+1) (Pair rho (Var k)) ((eval a rho):gam) U b
 (U,Sum bs) -> sequence_ [checkTUs k rho gam as | (_,as) <- bs]
 (Pi (Comp (Sum cas) nu) f,Fun ces) ->
   if map fst ces == map fst cas
     then sequence_ [ fix k rho gam as nu f c e | ((c,e), (_,as)) <- zip ces cas]
     else fail ("case branches does not match the data type")
 (Pi a f,Lam t) -> check (k+1) (Pair rho (Var k)) (a:gam) (app f (Var k)) t
 (_,Def e es as) -> do
      	             checkD k rho gam es as
                     let rho1 = PDef es as rho
                     check k rho1 (addC gam as rho (evals es rho1)) a e
 _ -> do
       a' <- checkI k rho gam t
       eqG a a'

vars k 0 = []
vars k l = (Var k):(vars (k+1) (pred l))

addC gam as nu [] = gam
addC gam (a:as) nu (u:us) =
 addC ((eval a nu):gam) as (Pair nu u) us

checkI k rho gam e = case e of
 Ref k -> return (gam !! k)
 App n m -> do
       	     c <- checkI k rho gam n
	     (a,f) <- extPi c
	     check k rho gam a m
	     return (app f (eval m rho))
 Def t es as -> do
  	         checkD k rho gam es as
                 let rho1 = PDef es as rho
                 checkI k rho1 (addC gam as rho (evals es rho1)) t
 _ -> Fail ("checkI " ++ show e)


extPi (Pi a b) = return (a,b)
extPi t = Fail (show t ++ " is not a product")

extSG c (Comp (Sum cas) r) =
 do
  as <- getG c cas
  return (as,r)
extSG c u = Fail ("extSG " ++ c ++ " " ++ show u)

extS c (Comp (Sum cas) r) = (get c cas,r)

get s [] = error ("get " ++ show s)     -- should never occur
get s ((s1,u):us) | s == s1 = u
get s ((s1,u):us)           = get s us

getG s [] = Fail ("getG " ++ show s)     -- should never occur
getG s ((s1,u):us) | s == s1 = return u
getG s ((s1,u):us)           = getG s us

checks :: Int -> Env -> [Exp] -> [Exp] -> Env -> [Exp] -> G ()

checks k rho gam [] _ [] = return ()
checks k rho gam (a:as) nu (e:es) =
 do 
  trace ("checking " ++ show e ++ "\n") (check k rho gam (eval a nu) e)
--  unsafePerformIO (print ("checking " ++ show e))
  checks k rho gam as (Pair nu (eval e rho)) es
checks k rho gam _ _ _ = Fail "checks"

