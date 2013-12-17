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

-- Branch of the form: c x1 .. xn -> e
type Brc = (Label,([String],Exp))

-- Telescope (x1 : A1) .. (xn : An)
type Tele = [(String,Exp)]

-- Labelled sum: c (x1 : A1) .. (xn : An)
type Lb  = [(Label,Tele)]

-- Mix values and expressions
type Val = Exp

-- Context gives type values to identifiers
type Ctxt = [(String,Val)]

-- Mutual recursive definitions: (x1 : A1) .. (xn : An) and x1 = e1 .. xn = en
type Def = (Tele,[(String,Exp)])

-- De Bruijn levels
mkVar :: Int -> Exp
mkVar k = Var (genName k)

genName :: Int -> String
genName n = "X" ++ show n

type Prim = (Integer,String)

data Exp = Comp Exp Env         -- for closures
         | App Exp Exp
         | Pi Exp Exp
         | Lam String Exp
         | Def Exp Def
         | Var String
         | U
         | Con String [Exp]
         | Fun Prim [Brc]
         | Sum Prim Lb
         | Undef Prim
         | EPrim Prim [Exp]     -- used for reification
  deriving (Eq,Show)

data Env = Empty
         | Pair Env (String,Val)
         | PDef Def Env         -- for handling recursive definitions,
                                -- see getE
  deriving (Eq,Show)

lets :: [Def] -> Exp -> Exp
lets []     e = e
lets (d:ds) e = Def (lets ds e) d

defs :: Env -> Exp -> Exp
defs Empty        e = e
defs (PDef d env) e = defs env (Def e d)
defs env          _ =
  error $ "defs: environment should a list of definitions " ++ show env

upds :: Env -> [(String,Val)] -> Env
upds env []       = env
upds env (xv:xvs) = upds (Pair env xv) xvs

eval :: Exp -> Env -> Val
eval (Def e d)   s = eval e (PDef d s)
eval (App t1 t2) s = app (eval t1 s) (eval t2 s)
eval (Pi a b)    s = Pi (eval a s) (eval b s)
eval (Con c ts)  s = Con c (map (\ e -> eval e s) ts)
eval (Var k)     s = getE k s
eval U           _ = U
eval t           s = Comp t s

evals :: [(String,Exp)] -> Env -> [(String,Val)]
evals es r = map (\(x,e) -> (x,eval e r)) es

app :: Val -> Val -> Val
app (Comp (Lam x b) s)     u            = eval b (Pair s (x,u))
app a@(Comp (Fun _ ces) r) b@(Con c us) = case lookup c ces of
  Just (xs,e)  -> eval e (upds r (zip xs us))
  Nothing -> error $ "app: " ++ show a ++ " " ++ show b
app f                      u            = App f u

getE :: String -> Env -> Exp
getE x (Pair _ (y,u)) | x == y       = u
getE x (Pair s _)                = getE x s
getE x r@(PDef d r1) = getE x (upds r1 (evals (snd d) r))

addC :: Ctxt -> (Tele,Env) -> [(String,Val)] -> Ctxt
addC gam _ [] = gam
addC gam (((y,a):as),nu) ((x,u):xus) =
  addC ((x,eval a nu):gam) (as,Pair nu (y,u)) xus

-- Extract the type of a label as a closure
getLblType :: String -> Exp -> Typing (Tele, Env)
getLblType c (Comp (Sum _ cas) r) = case lookup c cas of
  Just as -> return (as,r)
  Nothing -> throwError ("getLblType " ++ show c)
getLblType c u = throwError ("getLblType " ++ c ++ " " ++ show u)

-- Int is for de Bruijn levels
type LEnv = (Int,Env,Ctxt)

lEmpty :: LEnv
lEmpty = (0,Empty,[])

type Typing a = ReaderT LEnv (ErrorT String Identity) a

runTyping :: Typing a -> LEnv -> ErrorT String Identity a
runTyping = runReaderT

addType :: (String,Exp) -> LEnv -> LEnv
addType (x,a) lenv@(k,rho,gam) = addTypeVal (x,eval a rho) lenv

addTypeVal :: (String,Val) -> LEnv -> LEnv
addTypeVal (x,a) (k,rho,gam) = (k+1,Pair rho (x,mkVar k),(x,a):gam)

addBranch :: [(String,Val)] -> (Tele,Env) -> LEnv -> LEnv
addBranch nvs (tele,env) (k,rho,gam) = (k+l,upds rho nvs,addC gam (tele,env) nvs)
  where l = length nvs

addDef :: Def -> LEnv -> LEnv
addDef d@(ts,es) (k,rho,gam) =
  let rho1 = PDef d rho
  in (k,rho1,addC gam (ts,rho) (evals es rho1))

addTele :: Tele -> LEnv -> LEnv
addTele []          lenv = lenv
addTele (xa:xas) lenv = addTele xas (addType xa lenv)

getFresh :: Typing Exp
getFresh = do
  (k,_,_) <- ask
  return $ mkVar k

getIndex :: Typing Int
getIndex = do
  (k,_,_) <- ask
  return k

getEnv :: Typing Env
getEnv = do
  (_,rho,_) <- ask
  return rho

getCtxt :: Typing Ctxt
getCtxt = do
  (_,_,gam) <- ask
  return gam

(=?=) :: Typing Exp -> Exp -> Typing ()
m =?= s2 = do
  s1 <- m
  --trace ("comparing " ++ show s1 ++ " =?= " ++ show s2)
  unless (s1 == s2) $ throwError ("eqG " ++ show s1 ++ " =/= " ++ show s2)

checkDef :: Def -> Typing ()
checkDef (xas,xes) = trace ("checking definition " ++ show (map fst xes)) $ do
  checkTele xas
  rho <- getEnv
  local (addTele xas) $ checks (xas,rho) (map snd xes)

checkTele :: Tele -> Typing ()
checkTele []          = return ()
checkTele ((x,a):xas) = do
  check U a
  local (addType (x,a)) $ checkTele xas

check :: Val -> Exp -> Typing ()
check a t = case (a,t) of
  (_,Con c es) -> do
    (bs,nu) <- getLblType c a
    checks (bs,nu) es
  (U,Pi a (Lam x b)) -> do
    check U a
    local (addType (x,a)) $ check U b
  (U,Sum _ bs) -> sequence_ [checkTele as | (_,as) <- bs]
  (Pi (Comp (Sum _ cas) nu) f,Fun _ ces) ->
    if map fst ces == map fst cas
       then sequence_ [ checkBranch (as,nu) f brc
                      | (brc, (_,as)) <- zip ces cas ]
       else throwError "case branches does not match the data type"
  (Pi a f,Lam x t)  -> do
    var <- getFresh
    local (addTypeVal (x,a)) $ check (app f var) t
  (_,Def e d) -> do
    checkDef d
    local (addDef d) $ check a e
  (_,Undef _) -> return ()
  _ -> do
    k <- getIndex
    (reifyExp k <$> checkInfer t) =?= reifyExp k a

checkBranch :: (Tele,Env) -> Val -> Brc -> Typing ()
checkBranch (xas,nu) f (c,(xs,e)) = do
  k <- getIndex
  let l  = length xas
  let us = map mkVar [k..k+l-1]
  local (addBranch (zip xs us) (xas,nu)) $ check (app f (Con c us)) e

checkInfer :: Exp -> Typing Exp
checkInfer e = case e of
  U -> return U                 -- U : U
  Var n -> do
    gam <- getCtxt
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
  Def t d -> do
    checkDef d
    local (addDef d) $ checkInfer t
  _ -> throwError ("checkInfer " ++ show e)

checks :: (Tele,Env) -> [Exp] -> Typing ()
checks _              []     = return ()
checks ((x,a):xas,nu) (e:es) = do
  check (eval a nu) e
  rho <- getEnv
  checks (xas,Pair nu (x,eval e rho)) es
checks _              _      = throwError "checks"

-- Used in the interaction loop
runDefs :: LEnv -> [Def] -> Either String LEnv
runDefs = foldM runDef

runDef :: LEnv -> Def -> Either String LEnv
runDef lenv d = do
  runIdentity $ runErrorT $ runTyping (checkDef d) lenv
  return $ addDef d lenv

runInfer :: LEnv -> Exp -> Either String Exp
runInfer lenv e = do
  runIdentity $ runErrorT $ runTyping (checkInfer e) lenv

-- Reification of a value to an expression
reifyExp :: Int -> Val -> Exp
reifyExp _ U                     = U
reifyExp k (Comp (Lam x t) r)    = Lam (genName k) $ reifyExp (k+1) (eval t (Pair r (x,mkVar k)))
reifyExp k v@(Var l)             = v
reifyExp k (App u v)             = App (reifyExp k u) (reifyExp k v)
reifyExp k (Pi a f)              = Pi (reifyExp k a) (reifyExp k f)
reifyExp k (Con n ts)            = Con n (map (reifyExp k) ts)
reifyExp k (Comp (Fun prim _) r) = EPrim prim (reifyEnv k r)
reifyExp k (Comp (Sum prim _) r) = EPrim prim (reifyEnv k r)
reifyExp k (Comp (Undef prim) r) = EPrim prim (reifyEnv k r)

reifyEnv :: Int -> Env -> [Exp]
reifyEnv _ Empty          = []
reifyEnv k (Pair r (_,u)) = reifyEnv k r ++ [reifyExp k u] -- TODO: inefficient
reifyEnv k (PDef ts r)    = reifyEnv k r


-- Not used since we have U : U
-- checkTs :: [(String,Exp)] -> Typing ()
-- checkTs [] = return ()
-- checkTs ((x,a):xas) = do
--   checkType a
--   local (addType (x,a)) (checkTs xas)
--
-- checkType :: Exp -> Typing ()
-- checkType t = case t of
--   U              -> return ()
--   Pi a (Lam x b) -> do
--     checkType a
--     local (addType (x,a)) (checkType b)
--   _ -> checkInfer t =?= U
