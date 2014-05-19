module TypeChecker ( runDecls
                   , runDeclss
                   , runInfer
                   , TEnv(..)
                   , verboseEnv
                   , silentEnv
                   ) where

import Data.Either
import Data.Function
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
  b <- asks verbose
  when b $ liftIO (putStrLn s)

-- Type checking monad
type Typing a = ReaderT TEnv (ErrorT String IO) a

runTyping :: TEnv -> Typing a -> IO (Either String a)
runTyping env t = runErrorT $ runReaderT t env

-- Used in the interaction loop
runDecls :: TEnv -> ODecls -> IO (Either String TEnv)
runDecls tenv d = runTyping tenv $ do
  checkDecls d
  return $ addDecls d tenv

runDeclss :: TEnv -> [ODecls] -> IO (Maybe String,TEnv)
runDeclss tenv []         = return (Nothing, tenv)
runDeclss tenv (d:ds) = do
  x <- runDecls tenv d
  case x of
    Right tenv' -> runDeclss tenv' ds
    Left s      -> return (Just s, tenv)

runInfer :: TEnv -> Ter -> IO (Either String Val)
runInfer lenv e = runTyping lenv (checkInfer e)

addC :: Ctxt -> (Tele,OEnv) -> [(Binder,Val)] -> Ctxt
addC gam _             []          = gam
addC gam ((y,a):as,nu) ((x,u):xus) =
  let v = eval nu a
  in addC ((x,v):gam) (as,oPair nu (y,u)) xus

-- Extract the type of a label as a closure
getLblType :: String -> Val -> Typing (Tele, OEnv)
getLblType c (Ter (Sum _ cas) r) = case getIdent c cas of
  Just as -> return (as,r)
  Nothing -> throwError ("getLblType " ++ show c)
getLblType c u = throwError ("expected a data type for the constructor "
                             ++ c ++ " but got " ++ show u)

-- Environment for type checker
data TEnv = TEnv { index   :: Int   -- for de Bruijn levels
                 , oenv    :: OEnv
                 , ctxt    :: Ctxt
                 , verbose :: Bool  -- Should it be verbose and print
                                    -- what it typechecks?
                 }
  deriving (Eq,Show)

verboseEnv, silentEnv :: TEnv
verboseEnv = TEnv 0 oEmpty [] True
silentEnv  = TEnv 0 oEmpty [] False

addTypeVal :: (Binder,Val) -> TEnv -> TEnv
addTypeVal p@(x,_) (TEnv k rho gam v) =
  TEnv (k+1) (oPair rho (x,mkVar k (support rho))) (p:gam) v

addType :: (Binder,Ter) -> TEnv -> TEnv
addType (x,a) tenv@(TEnv _ rho _ _) = addTypeVal (x,eval rho a) tenv

addBranch :: [(Binder,Val)] -> (Tele,OEnv) -> TEnv -> TEnv
addBranch nvs (tele,env) (TEnv k rho gam v) =
  let e = addC gam (tele,env) nvs
  in TEnv (k + length nvs) (upds rho nvs) e v

addDecls :: ODecls -> TEnv -> TEnv
addDecls od@(ODecls d) (TEnv k rho gam v) =
  let rho1 = oPDef True od rho
      es'  = evals rho1 (declDefs d)
      gam' = addC gam (declTele d,rho) es'
  in TEnv k rho1 gam' v
addDecls od tenv = tenv {oenv = oPDef True od (oenv tenv)}

addTele :: Tele -> TEnv -> TEnv
addTele xas lenv = foldl (flip addType) lenv xas

getFresh :: Typing Val
getFresh = mkVar <$> asks index <*> (support <$> asks oenv)

checkDecls :: ODecls -> Typing ()
checkDecls (ODecls d) = do
  let (idents, tele, ters) = (declIdents d, declTele d, declTers d)
  trace ("Checking: " ++ unwords idents)
  checkTele tele
  rho <- asks oenv
  local (addTele tele) $ checks (tele,rho) ters
checkDecls _ = return ()

checkTele :: Tele -> Typing ()
checkTele []          = return ()
checkTele ((x,a):xas) = do
  check VU a
  local (addType (x,a)) $ checkTele xas

check :: Val -> Ter -> Typing ()
check a t = case (a,t) of
  (_,Con c es) -> do
    (bs,nu) <- getLblType c a
    checks (bs,nu) es
  (VU,Pi a (Lam x b)) -> do
    check VU a
    local (addType (x,a)) $ check VU b
  (VU,Sigma a (Lam x b)) -> do
    check VU a
    local (addType (x,a)) $ check VU b
  (VU,Sum _ bs) -> sequence_ [checkTele as | (_,as) <- bs]
  (VPi (Ter (Sum _ cas) nu) f,Split _ ces) -> do
    let cas' = sortBy (compare `on` fst . fst) cas
        ces' = sortBy (compare `on` fst) ces
    if map (fst . fst) cas' == map fst ces'
       then sequence_ [ checkBranch (as,nu) f brc
                      | (brc, (_,as)) <- zip ces' cas' ]
       else throwError "case branches does not match the data type"
  (VPi a f,Lam x t)  -> do
    var <- getFresh
    local (addTypeVal (x,a)) $ check (app f var) t
  (VSigma a f, SPair t1 t2) -> do
    check a t1
    e <- asks oenv
    check (app f (eval e t1)) t2
  (_,Where e d) -> do
    checkDecls d
    local (addDecls d) $ check a e
  (_,PN _) -> return ()
  _ -> do
    v <- checkInfer t
    k <- asks index
    unless (conv k v a) $
      throwError $ "check conv: " ++ show v ++ " /= " ++ show a

checkBranch :: (Tele,OEnv) -> Val -> Brc -> Typing ()
checkBranch (xas,nu) f (c,(xs,e)) = do
  k   <- asks index
  env <- asks oenv
  let d  = support env
      l  = length xas
      us = map (`mkVar` d) [k..k+l-1]
  local (addBranch (zip xs us) (xas,nu)) $ check (app f (VCon c us)) e

checkInfer :: Ter -> Typing Val
checkInfer e = case e of
  U -> return VU                 -- U : U
  Var n -> do
    gam <- asks ctxt
    case getIdent n gam of
      Just v  -> return v
      Nothing -> throwError $ show n ++ " is not declared!"
  App t u -> do
    c <- checkInfer t
    case c of
      VPi a f -> do
        check a u
        rho <- asks oenv
        return $ app f (eval rho u)
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
        e <- asks oenv
        return $ app f (fstSVal (eval e t))
      _          -> throwError $ show c ++ " is not a sigma-type"
  Where t d -> do
    checkDecls d
    local (addDecls d) $ checkInfer t
  _ -> throwError ("checkInfer " ++ show e)

checks :: (Tele,OEnv) -> [Ter] -> Typing ()
checks _              []     = return ()
checks ((x,a):xas,nu) (e:es) = do
  check (eval nu a) e
  rho <- asks oenv
  checks (xas,oPair nu (x,eval rho e)) es
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
