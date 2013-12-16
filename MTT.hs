-- miniTT, with recursive definitions
module MTT where

import Control.Monad
import Debug.Trace
import Control.Monad.Trans.Error hiding (fix,throwError)
import Control.Monad.Trans.Reader
import Control.Monad.Identity
import Control.Monad.Error (throwError)
import Control.Applicative


type Binder = String
type Label = String

-- TODO: hack
toBinder ::  String -> Binder
toBinder x = x

type Brc = [(Label,([String],Exp))]
type Lb  = [(Label,Tele)]

type Val = Exp

type Cont = [(String,Val)]

type Def = (Tele,[(String,Exp)])

type Tele = [(String,Exp)]

mVar :: Int -> Exp
mVar k = Ref (genName k)

genName :: Int -> String
genName n = "X" ++ show n

data Exp = Comp Exp Env
         | App Exp Exp
         | Pi Exp Exp
         | Lam String Exp
         | Def Exp Def		-- unit substitutions (strings names of definitions)
         | Ref String		-- use names
         | U
         | Con String [Exp]
         | Fun Brc
         | Sum Lb
         | PN String            -- primitive notion
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

-- data LEnv = LEnv
type LEnv = (Int,Env,Cont)

lEmpty :: LEnv
lEmpty = (0,Empty,[])

lets :: [Def] -> Exp -> Exp
lets [] e = e
lets (d:ds) e = Def (lets ds e) d

defs :: Env -> Exp -> Exp
defs Empty e = e
defs (PDef d env) e = defs env (Def e d)
defs env _ = error $ "defs: environment should a list of definitions "
             ++ show env

upds :: Env -> [(String,Val)] -> Env
upds env []          = env
upds env (xv:xvs) = upds (Pair env xv) xvs

eval :: Exp -> Env -> Val       -- eval is also composition!
eval (Def e d)   s = eval e (PDef d s)
eval (App t1 t2) s = app (eval t1 s) (eval t2 s)
eval (Pi a b)    s = Pi (eval a s) (eval b s)
eval (Con c ts)  s = Con c (map (\ e -> eval e s) ts)
eval (Ref k)     s = getE k s
eval U           _ = U
eval (PN n)      s = PN n
--eval (Comp t s')   s = eval t (compose s' s) -- ??
eval t           s = Comp t s

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

addC :: Cont -> (Tele,Env) -> [(String,Val)] -> Cont
addC gam _ [] = gam
addC gam (((y,a):as),nu) ((x,u):xus) =
  addC ((x,eval a nu):gam) (as,Pair nu (y,u)) xus

type Typing a = ReaderT LEnv (ErrorT String Identity) a

runTyping :: Typing a -> LEnv -> ErrorT String Identity a
runTyping = runReaderT

addType :: String -> Exp -> LEnv -> LEnv
addType x a (k,rho,gam) = (k+1,Pair rho (x,mVar k),(x,eval a rho):gam)

addTypeVal :: String -> Val -> LEnv -> LEnv
addTypeVal x a (k,rho,gam) = (k+1,Pair rho (x,mVar k),(x,a):gam)

addBranch :: [(String,Val)] -> (Tele,Env) -> LEnv -> LEnv
addBranch nvs (tele,env) (k,rho,gam) = (k+l,upds rho nvs,addC gam (tele,env) nvs)
  where l = length nvs

addDef :: Def -> LEnv -> LEnv
addDef d@(ts,es) (k,rho,gam) =
  let rho1 = PDef d rho
  in (k,rho1,addC gam (ts,rho) (evals es rho1))

addTele :: Tele -> LEnv -> LEnv
addTele []          lenv = lenv
addTele ((x,a):xas) lenv = addTele xas (addType x a lenv)

getFresh :: Typing Exp
getFresh = do
  (k,_,_) <- ask
  return $ mVar k

getIndex :: Typing Int
getIndex = do
  (k,_,_) <- ask
  return k

getEnv :: Typing Env
getEnv = do
  (_,rho,_) <- ask
  return rho

getCont :: Typing Cont
getCont = do
  (_,_,gam) <- ask
  return gam

(=?=) :: Typing Exp -> Exp -> Typing ()
m =?= s2 = do
  s1 <- m
  --trace ("comparing " ++ show s1 ++ " =?= " ++ show s2)
  unless (s1 == s2) $ throwError ("eqG " ++ show s1 ++ " =/= " ++ show s2)

checkDef :: Def -> Typing ()
checkDef (xas,xes) = do
  checkTs xas
  rho <- getEnv
  local (addTele xas) $ checks (xas,rho) (map snd xes)

checkTs :: [(String,Exp)] -> Typing ()
checkTs [] = return ()
checkTs ((x,a):xas) = do
  checkT a
  local (addType x a) (checkTs xas)

checkT :: Exp -> Typing ()
checkT t = case t of
  U              -> return ()
  Pi a (Lam x b) -> do
    checkT a
    local (addType x a) (checkT b)
  _ -> checkInfer t =?= U

check :: Val -> Exp -> Typing ()
check a t = case (a,t) of
  (Top,Top)    -> return ()
  (_,Con c es) -> do
    (bs,nu) <- extSG c a
    checks (bs,nu) es
  (U,Pi a (Lam x b)) -> do
    check U a
    local (addType x a) $ check U b
  (U,Sum bs) -> sequence_ [checkTele as | (_,as) <- bs]
  (Pi (Comp (Sum cas) nu) f,Fun ces) ->
    if map fst ces == map fst cas
       then sequence_ [ checkBranch as nu f c xs e
                      | ((c,(xs,e)), (_,as)) <- zip ces cas ]
       else throwError "case branches does not match the data type"
  (Pi a f,Lam x t)  -> do
    var <- getFresh
    local (addTypeVal x a) $ check (app f var) t
  (_,Def e d@(_,es)) -> trace ("checking definition " ++ show (map fst es))
    (do
      checkDef d
      local (addDef d) $ check a e)
  (_,PN _) -> return ()
  (_,Undef _) -> return ()
  _ -> do
    k <- getIndex
    (reifyExp k <$> checkInfer t) =?= reifyExp k a

checkTele :: Tele -> Typing ()
checkTele []          = return ()
checkTele ((x,a):xas) = do
  check U a
  local (addType x a) $ checkTele xas

checkBranch :: Tele -> Env -> Val -> String -> [String] -> Exp -> Typing ()
checkBranch xas nu f c xs e = do
  k <- getIndex
  let l  = length xas
  let us = map mVar [k..k+l-1]
  local (addBranch (zip xs us) (xas,nu)) $ check (app f (Con c us)) e

extSG :: String -> Exp -> Typing (Tele, Env)
extSG c (Comp (Sum cas) r) = case lookup c cas of
  Just as -> return (as,r)
  Nothing -> throwError ("extSG " ++ show c)
extSG c u = throwError ("extSG " ++ c ++ " " ++ show u)

checkInfer :: Exp -> Typing Exp
checkInfer e = case e of
  U -> return U                 -- U : U
  Ref n -> do
    gam <- getCont
    case lookup n gam of
      Just v  -> return v
      Nothing -> throwError $ show n ++ " is not declared!"
  App t u -> do
    c <- checkInfer t
    case c of
      Pi a f -> do
        check a u
        rho <- getEnv
        return (app f (eval u rho))
      _      ->  throwError $ show c ++ " is not a product"
  Def t d@(_,es) -> trace ("checking definition " ++ show (map fst es))
    (do
      checkDef d
      local (addDef d) $ checkInfer t)
  _ -> throwError ("checkInfer " ++ show e)



checks :: (Tele,Env) -> [Exp] -> Typing ()
checks _  []     = return ()
checks ((x,a):xas,nu) (e:es) = do
  -- trace ("checking " ++ show e ++ "\nof type " ++ show a
  --        ++ "\nin " ++ show rho ++ "\n")
  check (eval a nu) e
  rho <- getEnv
  checks (xas,Pair nu (x,eval e rho)) es
checks _ _ = throwError "checks"


runDefs :: LEnv -> [Def] -> Either String LEnv
runDefs = foldM runDef

runDef :: LEnv -> Def -> Either String LEnv
runDef lenv d = do
  runIdentity $ runErrorT $ runTyping (checkDef d) lenv
  return $ addDef d lenv

runInfer :: LEnv -> Exp -> Either String Exp
runInfer lenv e = do
  runIdentity $ runErrorT $ runTyping (checkInfer e) lenv

-- type Typing a = ReaderT LEnv (ErrorT String Identity) a

-- runTyping :: Typing a -> LEnv -> ErrorT String Identity a
-- runTyping = runReaderT


-- checkExp :: Exp -> Typing ()
-- checkExp = check 0 Empty [] Top

-- checkExpType :: Exp -> Exp -> Typing ()
-- checkExpType t a = check a t

-- checkExpInfer :: Exp -> Typing ()
-- checkExpInfer t = do
--   a <- checkInfer t
--   checkExpType t a

-- Reification of a value to a term
reifyExp :: Int -> Exp -> Exp
reifyExp _ Top                = Top
reifyExp _ U                  = U
reifyExp k (Comp (Lam x t) r) = Lam (genName k) $ reifyExp (k+1) (eval t (Pair r (x,mVar k)))
reifyExp k v@(Ref l)          = v
reifyExp k (App u v)          = App (reifyExp k u) (reifyExp k v)
reifyExp k (Pi a f)           = Pi (reifyExp k a) (reifyExp k f)
reifyExp k (Con n ts)         = Con n (map (reifyExp k) ts)
reifyExp k (Comp (Fun bs) r)  = EPrim (PFun bs) (reifyEnv k r)
reifyExp k (Comp (Sum ls) r)  = EPrim (PSum ls) (reifyEnv k r)
reifyExp k (Comp (Undef l) r) = EPrim (PUndef l) (reifyEnv k r)
reifyExp k (PN n)             = PN n

reifyEnv :: Int -> Env -> [Exp]
reifyEnv _ Empty       = []
reifyEnv k (Pair r (_,u))  = reifyEnv k r ++ [reifyExp k u] -- TODO: inefficient
reifyEnv k (PDef ts r) = reifyEnv k r



