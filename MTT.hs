-- nameless miniTT, with recursive definitions
module MTT where

import Control.Monad
import Debug.Trace
import Control.Monad.Error hiding (Error,fix)
import Control.Applicative

type Brc = [(String,([String],Exp))]
type Lb  = [(String,[Exp])]

type Val = Exp

type Cont = [(String,Val)]

type Def = ([(String,Exp)],[(String,Exp)])


data Exp = Comp Exp Env
         | App Exp Exp
         | Pi Exp Exp
         | Lam String Exp
         | Def Exp Def		-- unit substitutions (strings names of definitions)
         | Var Int 		-- generic values
         | Ref String		-- use names
         | U
         | Con String [Exp]
         | Fun Brc
         | Sum Lb
         | PN String Exp        -- primitive notion (typed)
         | Top
         | Undef Integer
         | EPrim Prim [Exp]  
  deriving (Eq,Show)

data Prim = PFun Brc
          | PSum Lb
          | PUndef Integer
  deriving (Eq,Show)            

data Env = Empty
         | Pair Env String Val
         | PDef Def Env
  deriving (Eq,Show)

upds :: Env -> [(String,Val)] -> Env
upds [] env = env
upds ((x,v):xvs) env = upds xvs (Pair env x v)

eval :: Exp -> Env -> Val       -- eval is also composition!
eval (Def env d) s     = eval e (PDef d env)
eval (App t1 t2)     s = app (eval t1 s) (eval t2 s)
eval (Pi a b)        s = Pi (eval a s) (eval b s)
eval (Con c ts)    s   = Con c (evals ts s)
eval (Ref k)       s   = getE k s
eval U             _   = U
eval (PN n a)      s   = PN n (eval a s)
--eval (Comp t s')   s = eval t (compose s' s) -- ??
eval t             s   = Comp t s

evals :: [(String,Exp)] -> Env -> [(String,Val)]
evals es r = map (\(x,e) -> (x,eval e r)) es

app :: Val -> Val -> Val
app (Comp (Lam x b) s)     u            = eval b (Pair s x u)
app a@(Comp (Fun _ ces) r) b@(Con c us) = case lookup c ces of
  Just (xs,e)  -> eval e (upds r (zip xs us))
  Nothing -> error $ "app: " ++ show a ++ " " ++ show b
app f                    u            = App f u

getE :: String -> Env -> Exp
getE x (Pair _ y u) | x == y       = u
getE x (Pair s _ _)                = getE (pred k) s
getE l r@(PDef es r1) = getE l (upds r1 (evals (map fst es) r))

addC :: Cont -> [Exp] -> Env -> [(String,Val)] -> Cont
addC gam _      _  []     = gam
addC gam (a:as) nu ((x,u):xus) = addC (eval a nu:gam) as (Pair nu x u) us

-- An error monad
type Error a = Either String a

(=?=) :: Error Exp -> Exp -> Error ()
m =?= s2 = do
  s1 <- m
  --trace ("comparing " ++ show s1 ++ " =?= " ++ show s2)
  unless (s1 == s2) $ Left ("eqG " ++ show s1 ++ " =/= " ++ show s2)

checkD :: Int -> Env -> Cont -> Def -> Error ()
checkD k rho gam (as,es) = do
  (rho1,gam1,l) <- checkTs k rho gam as
  checks l rho1 gam1 as rho es

checkTs :: Int -> Env -> Cont -> [(String,Exp)] -> Error (Env,Cont,Int)
checkTs k rho gam []     = return (rho,gam,k)
checkTs k rho gam ((x,a):xas) = do
  checkT k rho gam a
  checkTs (k+1) (Pair rho x (Var k)) ((x,eval a rho):gam) as

checkT :: Int -> Env -> Cont -> Exp -> Error ()
checkT k rho gam t = case t of
  U            -> return ()
  Pi a (Lam x b) -> do
    checkT k rho gam a
    checkT (k+1) (Pair rho x (Var k)) ((x,eval a rho):gam) b
  _ -> checkI k rho gam t =?= U

check :: Int -> Env -> Cont -> Val -> Exp -> Error ()
check k rho gam a t = case (a,t) of
  (Top,Top)    -> return ()
  (_,Con c es) -> do
    (bs,nu) <- extSG c a
    checks k rho gam bs nu es
  (U,Pi a (Lam x b)) -> do
    check k rho gam U a
    check (k+1) (Pair rho x (Var k)) ((x,eval a rho):gam) U b
  (U,Sum bs) -> sequence_ [checkTUs k rho gam as | (_,as) <- bs]
  (Pi (Comp (Sum cas) nu) f,Fun _ ces) ->
    if map fst ces == map fst cas
       then sequence_ [ fix k rho gam as nu f c e
                      | ((c,e), (_,as)) <- zip ces cas]
       else fail "case branches does not match the data type"
  (Pi a f,Lam x t)  -> check (k+1) (Pair rho x (Var k)) ((x,a):gam) (app f (Var k)) t
  (_,Def e (ts,es)) -> -- trace ("checking definition " ++ show str)
    (do
      checkD k rho gam d
      let rho1 = PDef d rho
      check k rho1 (addC gam (map snd ts) rho (evals es rho1)) a e)
  (t,Undef n) -> return ()                       
  _ -> do
    (reifyExp k <$> checkI k rho gam t) =?= reifyExp k a

checkTUs :: Int -> Env -> Cont -> [(String,Exp)] -> Error ()
checkTUs _ _   _   []     = return ()
checkTUs k rho gam ((x,a):xas) = do
  check k rho gam U a
  checkTUs (k+1) (Pair rho x (Var k)) ((x,eval a rho):gam) as

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
  U -> return U                 -- U : U
  Ref k   -> return (gam !! k)
  App n m -> do
    c <- checkI k rho gam n
    case c of
      Pi a f -> do
        check k rho gam a m
        return (app f (eval m rho))
      _      ->  Left $ show c ++ " is not a product"
  Def t es str -> trace ("checking definition " ++ show str)
    (do
      checkD k rho gam es
      let rho1 = PDef es rho
      checkI k rho1 (addC gam (map snd es) rho (evals (map fst es) rho1)) t)
  PN _ a -> do
    checkT k rho gam a          -- ??
    return (eval a rho)
  _ -> Left ("checkI " ++ show e ++ " in " ++ show rho)


checks :: Int -> Env -> [Exp] -> [Exp] -> Env -> [Exp] -> Error ()
checks _ _   _    []    _  []     = return ()
checks k rho gam (a:as) nu (e:es) = do
  -- trace ("checking " ++ show e ++ "\nof type " ++ show a
  --        ++ "\nin " ++ show rho ++ "\n")
  check k rho gam (eval a nu) e
  checks k rho gam as (Pair nu (eval e rho)) es
checks k rho gam _ _ _ = Left "checks"


checkExp :: Exp -> Error ()
checkExp = check 0 Empty [] Top

checkExpType :: Exp -> Exp -> Error ()
checkExpType t a = check 0 Empty [] a t

checkExpInfer :: Exp -> Error ()
checkExpInfer t = do
  a <- checkI 0 Empty [] t
  checkExpType t a


-- Reification of a value to a term
reifyExp :: Int -> Exp -> Exp
reifyExp _ Top                 = Top
reifyExp _ U                   = U
reifyExp k (Comp (Lam x t) r)  = Lam $ reifyExp (k+1) (eval t (Pair r x (Var k)))
reifyExp k (Var l)             = Ref (k-l-1)
reifyExp k (App u v)           = App (reifyExp k u) (reifyExp k v)
reifyExp k (Pi a f)            = Pi (reifyExp k a) (reifyExp k f)
reifyExp k (Con n ts)          = Con n (map (reifyExp k) ts)
reifyExp k (Comp (Fun bs) r)   = EPrim (PFun bs) (reifyEnv k r)
reifyExp k (Comp (Sum ls) r)   = EPrim (PSum ls) (reifyEnv k r)
reifyExp k (Comp (Undef l) r)  = EPrim (PUndef l) (reifyEnv k r)
reifyExp k (PN n a)            = PN n (reifyExp k a)

reifyEnv :: Int -> Env -> [Exp]
reifyEnv _ Empty       = []
reifyEnv k (Pair r u)  = reifyEnv k r ++ [reifyExp k u] -- TODO: inefficient
reifyEnv k (PDef ts r) = reifyEnv k r


