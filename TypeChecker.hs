module TypeChecker ( runDef
                   , runDefs
                   , runInfer
                   , TEnv(..)
                   , verboseEnv
                   , silentEnv
                   ) where

import Data.Either
import Data.List
import Data.Maybe
import Data.Monoid hiding (Sum)
import Control.Monad
import Control.Monad.Trans
import Control.Monad.Trans.Error hiding (throwError)
import Control.Monad.Trans.Reader
import Control.Monad.Error (throwError)
import Control.Applicative
import Pretty

import CTT
import Eval

trace :: String -> Typing ()
trace s = do
  b <- getVerbose
  if b then liftIO (putStrLn s) else return ()

-- Type checking monad
type Typing a = ReaderT TEnv (ErrorT String IO) a

runTyping :: Typing a -> TEnv -> IO (Either String a)
runTyping t env = runErrorT $ runReaderT t env

-- Used in the interaction loop
runDef :: TEnv -> Def -> IO (Either String TEnv)
runDef lenv d = flip runTyping lenv $ do
  checkDef d
  addDef d lenv

runDefs :: TEnv -> [Def] -> IO (Maybe String,TEnv)
runDefs tenv []     = return $ (Nothing, tenv)
runDefs tenv (d:ds) = do
  x   <- runDef tenv d
  case x of
    Right tenv' -> runDefs tenv' ds
    Left s      -> return $ (Just s , tenv)

runInfer :: TEnv -> Ter -> IO (Either String Val)
runInfer lenv e = runTyping (checkInfer e) lenv

eval :: Env -> Ter -> Typing Val
eval env ter = do
  b <- getDebug
  return $ evalTer b env ter

app :: Val -> Val -> Typing Val
app v1 v2 = do
  b <- getDebug
  return $ appVal b v1 v2

evals :: Env -> [(Binder,Ter)] -> Typing [(Binder,Val)]
evals rho t = do
  b <- getDebug
  return $ evalTers b rho t

conv :: Int -> Val -> Val -> Typing Bool
conv k v1 v2 = do
  b <- getDebug
  return $ convVal b k v1 v2

addC :: Ctxt -> (Tele,Env) -> [(String,Val)] -> Typing Ctxt
addC gam _             []          = return gam
addC gam ((y,a):as,nu) ((x,u):xus) = do
  v <- eval nu a
  addC ((x,v):gam) (as,Pair nu (y,u)) xus

-- Extract the type of a label as a closure
getLblType :: String -> Val -> Typing (Tele, Env)
getLblType c (Ter (Sum _ cas) r) = case lookup c cas of
  Just as -> return (as,r)
  Nothing -> throwError ("getLblType " ++ show c)
getLblType c u = throwError ("expected a data type for the constructor "
                             ++ c ++ " but got " ++ show u)

-- Environment for type checker
data TEnv = TEnv { index   :: Int   -- for de Bruijn levels
                 , env     :: Env
                 , ctxt    :: Ctxt
                 , verbose :: Bool  -- Should it be verbose and print
                                    -- what it typechecks?
                 , debug   :: Bool  -- Should the evaluator be run in
                                    -- debug mode?
                 }
  deriving (Eq,Show)

verboseEnv :: Bool -> TEnv
verboseEnv debug = TEnv 0 Empty [] True debug

silentEnv :: TEnv
silentEnv = TEnv 0 Empty [] False False

addTypeVal :: (String,Val) -> TEnv -> TEnv
addTypeVal p@(x,_) (TEnv k rho gam v d) =
  TEnv (k+1) (Pair rho (x,mkVar k (support rho))) (p:gam) v d

addType :: (String,Ter) -> TEnv -> Typing TEnv
addType (x,a) tenv@(TEnv _ rho _ _ _) = do
  v <- eval rho a
  return $ addTypeVal (x,v) tenv

addBranch :: [(String,Val)] -> (Tele,Env) -> TEnv -> Typing TEnv
addBranch nvs (tele,env) (TEnv k rho gam v d) = do
  e <- addC gam (tele,env) nvs
  return $ TEnv (k + length nvs) (upds rho nvs) e v d

addDef :: Def -> TEnv -> Typing TEnv
addDef d@(ts,es) (TEnv k rho gam v b) = do
  let rho1 = PDef es rho
  es'  <- evals rho1 es
  gam' <- addC gam (ts,rho) es'
  return $ TEnv k rho1 gam' v b

addTele :: Tele -> TEnv -> Typing TEnv
addTele xas lenv = foldM (flip addType) lenv xas

-- Useful monadic versions of functions:
checkM :: Typing Val -> Ter -> Typing ()
checkM v t = do
  v' <- v
  check v' t

localM :: (TEnv -> Typing TEnv) -> Typing a -> Typing a
localM f r = do
  e <- ask
  a <- f e
  local (const a) r

-- Getters:
getIndex :: Typing Int
getIndex = index <$> ask

getDebug :: Typing Bool
getDebug = debug <$> ask

getVerbose :: Typing Bool
getVerbose = verbose <$> ask

getFresh :: Typing Val
getFresh = do
    e <- getEnv
    k <- getIndex
    return $ mkVar k (support e)

getEnv :: Typing Env
getEnv = env <$> ask

getCtxt :: Typing Ctxt
getCtxt = ctxt <$> ask

-- The typechecker:
checkDef :: Def -> Typing ()
checkDef (xas,xes) = do
  trace ("Checking definition: " ++ unwords (map fst xes))
  checkTele xas
  rho <- getEnv
  localM (addTele xas) $ checks (xas,rho) (map snd xes)

checkTele :: Tele -> Typing ()
checkTele []          = return ()
checkTele ((x,a):xas) = do
  check VU a
  localM (addType (x,a)) $ checkTele xas

check :: Val -> Ter -> Typing ()
check a t = case (a,t) of
  (_,Con c es) -> do
    (bs,nu) <- getLblType c a
    checks (bs,nu) es
  (VU,Pi a (Lam x b)) -> do
    check VU a
    localM (addType (x,a)) $ check VU b
  (VU,Sigma a (Lam x b)) -> do
    check VU a
    localM (addType (x,a)) $ check VU b
  (VU,Sum _ bs) -> sequence_ [checkTele as | (_,as) <- bs]
  (VPi (Ter (Sum _ cas) nu) f,Split _ ces) ->
    if sort (map fst ces) == sort (map fst cas)
       then sequence_ [ checkBranch (as,nu) f brc
                      | (brc, (_,as)) <- zip ces cas ]
       else throwError "case branches does not match the data type"
  (VPi a f,Lam x t)  -> do
    var <- getFresh
    local (addTypeVal (x,a)) $ checkM (app f var) t
  (VSigma a f, SPair t1 t2) -> do
    check a t1
    e <- getEnv
    v <- eval e t1
    checkM (app f v) t2
  (_,Where e d) -> do
    checkDef d
    localM (addDef d) $ check a e
  (_,PN _) -> return ()
  _ -> do
    v <- checkInfer t
    k <- getIndex
    b <- conv k v a
    unless b $
      throwError $ "check conv: " ++ show v ++ " /= " ++ show a

checkBranch :: (Tele,Env) -> Val -> Brc -> Typing ()
checkBranch (xas,nu) f (c,(xs,e)) = do
  k     <- getIndex
  env   <- getEnv
  let d  = support env
  let l  = length xas
  let us = map (`mkVar` d) [k..k+l-1]
  localM (addBranch (zip xs us) (xas,nu)) $ checkM (app f (VCon c us)) e

checkInfer :: Ter -> Typing Val
checkInfer e = case e of
  U -> return VU                 -- U : U
  Var n -> do
    gam <- getCtxt
    case lookup n gam of
      Just v  -> return v
      Nothing -> throwError $ show n ++ " is not declared!"
  App t u -> do
    c <- checkInfer t
    case c of
      VPi a f -> do
        check a u
        rho <- getEnv
        v   <- eval rho u
        app f v
      _       -> throwError $ show c ++ " is not a product"
  Fst t -> do
    c <- checkInfer t
    case c of
      VSigma a f -> return a
      _          -> throwError $ show c ++ " is not a sigma-type"
  Snd t -> do
    c <- checkInfer t
    case c of
      VSigma a f -> do
        e <- getEnv
        v <- eval e t
        app f (fstSVal v)
      _          -> throwError $ show c ++ " is not a sigma-type"
  Where t d -> do
    checkDef d
    localM (addDef d) $ checkInfer t
  _ -> throwError ("checkInfer " ++ show e)

checks :: (Tele,Env) -> [Ter] -> Typing ()
checks _              []     = return ()
checks ((x,a):xas,nu) (e:es) = do
  v <- eval nu a
  check v e
  rho <- getEnv
  v' <- eval rho e
  checks (xas,Pair nu (x,v')) es
checks _              _      = throwError "checks"

-- Not used since we have U : U
--
-- (=?=) :: Typing Ter -> Ter -> Typing ()
-- m =?= s2 = do
--   s1 <- m
--   unless (s1 == s2) $ throwError (show s1 ++ " =/= " ++ show s2)
--
-- checkTs :: [(String,Ter)] -> Typing ()
-- checkTs [] = return ()
-- checkTs ((x,a):xas) = do
--   checkType a
--   local (addType (x,a)) (checkTs xas)
--
-- checkType :: Ter -> Typing ()
-- checkType t = case t of
--   U              -> return ()
--   Pi a (Lam x b) -> do
--     checkType a
--     local (addType (x,a)) (checkType b)
--   _ -> checkInfer t =?= U
