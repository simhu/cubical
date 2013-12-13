-- miniTT, with recursive definitions
module MTT where

import Control.Monad
import Debug.Trace
import Control.Monad.Error hiding (Error,fix)
import Control.Applicative

type Brc = [(String,([String],Exp))]
type Lb  = [(String,Tele)]

type Val = Exp

type Cont = [(String,Val)]

type Def = (Tele,[(String,Exp)])

type Binder = String

type Tele = [(String,Exp)]

mVar :: Int -> Exp
mVar k = Ref (genName k)

genName :: Int -> Binder
genName n = "X" ++ show n

data Exp = Comp Exp Env
         | App Exp Exp
         | Pi Exp Exp
         | Lam Binder Exp
         | Def Exp Def		-- unit substitutions (strings names of definitions)
--         | Var Int 		-- generic values
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
         | Pair Env (String,Val)
         | PDef Def Env
  deriving (Eq,Show)

upds :: Env -> [(String,Val)] -> Env
upds env []          = env
upds env (xv:xvs) = upds (Pair env xv) xvs

eval :: Exp -> Env -> Val       -- eval is also composition!
eval (Def e d) s     = eval e (PDef d s)
eval (App t1 t2) s = app (eval t1 s) (eval t2 s)
eval (Pi a b)    s = Pi (eval a s) (eval b s)
eval (Con c ts)    s   = Con c (map (\ e -> eval e s) ts)
eval (Ref k)       s   = getE k s
eval U             _   = U
eval (PN n a)      s   = PN n (eval a s)
--eval (Comp t s')   s = eval t (compose s' s) -- ??
eval t             s   = Comp t s

evals :: [(String,Exp)] -> Env -> [(String,Val)]
evals es r = map (\(x,e) -> (x,eval e r)) es

app :: Val -> Val -> Val
app (Comp (Lam x b) s)     u            = eval b (Pair s (x,u))
app a@(Comp (Fun ces) r) b@(Con c us) = case lookup c ces of
  Just (xs,e)  -> eval e (upds r (zip xs us))
  Nothing -> error $ "app: " ++ show a ++ " " ++ show b
app f                    u            = App f u

getE :: String -> Env -> Exp
getE x (Pair _ (y,u)) | x == y       = u
getE x (Pair s _)                = getE x s
getE x r@(PDef d r1) = getE x (upds r1 (evals (snd d) r))

addC :: Cont -> Tele -> Env -> [(String,Val)] -> Cont
addC gam _      _  []     = gam
addC gam ((y,a):as) nu ((x,u):xus) = addC ((x,eval a nu):gam) as (Pair nu (y,u)) xus

-- An error monad
type Error a = Either String a

(=?=) :: Error Exp -> Exp -> Error ()
m =?= s2 = do
  s1 <- m
  --trace ("comparing " ++ show s1 ++ " =?= " ++ show s2)
  unless (s1 == s2) $ Left ("eqG " ++ show s1 ++ " =/= " ++ show s2)

checkD :: Int -> Env -> Cont -> Def -> Error ()
checkD k rho gam (xas,xes) = do
  (rho1,gam1,l) <- checkTs k rho gam xas
  checks l rho1 gam1 xas rho (map snd xes)

checkTs :: Int -> Env -> Cont -> [(String,Exp)] -> Error (Env,Cont,Int)
checkTs k rho gam []     = return (rho,gam,k)
checkTs k rho gam ((x,a):xas) = do
  checkT k rho gam a
  checkTs (k+1) (Pair rho (x,mVar k)) ((x,eval a rho):gam) xas

checkT :: Int -> Env -> Cont -> Exp -> Error ()
checkT k rho gam t = case t of
  U            -> return ()
  Pi a (Lam x b) -> do
    checkT k rho gam a
    checkT (k+1) (Pair rho (x,mVar k)) ((x,eval a rho):gam) b
  _ -> checkI k rho gam t =?= U

check :: Int -> Env -> Cont -> Val -> Exp -> Error ()
check k rho gam a t = case (a,t) of
  (Top,Top)    -> return ()
  (_,Con c es) -> do
    (bs,nu) <- extSG c a
    checks k rho gam bs nu es
  (U,Pi a (Lam x b)) -> do
    check k rho gam U a
    check (k+1) (Pair rho (x,mVar k)) ((x,eval a rho):gam) U b
  (U,Sum bs) -> sequence_ [checkTUs k rho gam as | (_,as) <- bs]
  (Pi (Comp (Sum cas) nu) f,Fun ces) ->
    if map fst ces == map fst cas
       then sequence_ [ checkBranch k rho gam as nu f c xs e
                      | ((c,(xs,e)), (_,as)) <- zip ces cas ]
       else fail "case branches does not match the data type"
  (Pi a f,Lam x t)  -> check (k+1) (Pair rho (x,mVar k)) ((x,a):gam) (app f (mVar k)) t
  (_,Def e d@(ts,es)) -> -- trace ("checking definition " ++ show str)
    (do
      checkD k rho gam d
      let rho1 = PDef d rho
      check k rho1 (addC gam ts rho (evals es rho1)) a e)
  (t,Undef n) -> return ()
  _ -> do
    (reifyExp k <$> checkI k rho gam t) =?= reifyExp k a

checkTUs :: Int -> Env -> Cont -> Tele -> Error ()
checkTUs _ _   _   []     = return ()
checkTUs k rho gam ((x,a):xas) = do
  check k rho gam U a
  checkTUs (k+1) (Pair rho (x,mVar k)) ((x,eval a rho):gam) xas

--addC :: Cont -> [Exp] -> Env -> [(String,Val)] -> Cont
-- What does this do?
checkBranch :: Int -> Env -> Cont -> Tele -> Env -> Val -> String -> [Binder] -> Exp -> Error ()
checkBranch k rho gam xas nu f c xs e = do
  let l  = length xas
  let us = map mVar [k..k+l-1]
  check (k+l) (upds rho (zip xs us)) (addC gam xas nu (zip xs us)) (app f (Con c us)) e

extSG :: String -> Exp -> Error (Tele, Env)
extSG c (Comp (Sum cas) r) = case lookup c cas of
  Just as -> return (as,r)
  Nothing -> Left ("extSG " ++ show c)
extSG c u = Left ("extSG " ++ c ++ " " ++ show u)

checkI :: Int -> Env -> Cont -> Exp -> Error Exp
checkI k rho gam e = case e of
  U -> return U                 -- U : U
  Ref k   -> case lookup k gam of
    Just v  -> return v
    Nothing -> Left $ show k ++ " is not declared!"
  App n m -> do
    c <- checkI k rho gam n
    case c of
      Pi a f -> do
        check k rho gam a m
        return (app f (eval m rho))
      _      ->  Left $ show c ++ " is not a product"
  Def t d@(xas,xes) -> -- trace ("checking definition " ++ show str)
    (do
      checkD k rho gam d
      let rho1 = PDef d rho
      checkI k rho1 (addC gam xas rho (evals xes rho1)) t)
  PN _ a -> do
    checkT k rho gam a          -- ??
    return (eval a rho)
  _ -> Left ("checkI " ++ show e ++ " in " ++ show rho)


checks :: Int -> Env -> Cont -> Tele -> Env -> [Exp] -> Error ()
checks _ _   _    []    _  []     = return ()
checks k rho gam ((x,a):xas) nu (e :es) = do
  -- trace ("checking " ++ show e ++ "\nof type " ++ show a
  --        ++ "\nin " ++ show rho ++ "\n")
  check k rho gam (eval a nu) e
  checks k rho gam xas (Pair nu (x,eval e rho)) es
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
reifyExp k (Comp (Lam x t) r)  = Lam (genName k) $ reifyExp (k+1) (eval t (Pair r (x,mVar k)))
reifyExp k v@(Ref l)           = v
reifyExp k (App u v)           = App (reifyExp k u) (reifyExp k v)
reifyExp k (Pi a f)            = Pi (reifyExp k a) (reifyExp k f)
reifyExp k (Con n ts)          = Con n (map (reifyExp k) ts)
reifyExp k (Comp (Fun bs) r)   = EPrim (PFun bs) (reifyEnv k r)
reifyExp k (Comp (Sum ls) r)   = EPrim (PSum ls) (reifyEnv k r)
reifyExp k (Comp (Undef l) r)  = EPrim (PUndef l) (reifyEnv k r)
reifyExp k (PN n a)            = PN n (reifyExp k a)

reifyEnv :: Int -> Env -> [Exp]
reifyEnv _ Empty       = []
reifyEnv k (Pair r (_,u))  = reifyEnv k r ++ [reifyExp k u] -- TODO: inefficient
reifyEnv k (PDef ts r) = reifyEnv k r


