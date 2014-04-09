module TypeChecker ( runDecls
                   , runDeclss
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
  b <- verbose <$> ask
  when b $ liftIO (putStrLn s)

-- Type checking monad
type Typing a = ReaderT TEnv (ErrorT String Eval) a

runTyping :: Bool -> TEnv -> Typing a -> IO (Either String a)
runTyping debug env t = runEval debug $ runErrorT $ runReaderT t env

-- Used in the interaction loop
runDecls :: Bool -> TEnv -> ODecls -> IO (Either String TEnv)
runDecls debug tenv d = runTyping debug tenv $ do
  checkDecls d
  addDecls d tenv

runDeclss :: Bool -> TEnv -> [ODecls] -> IO (Maybe String,TEnv)
runDeclss _ tenv []         = return (Nothing, tenv)
runDeclss debug tenv (d:ds) = do
  x <- runDecls debug tenv d
  case x of
    Right tenv' -> runDeclss debug tenv' ds
    Left s      -> return (Just s, tenv)

runInfer :: Bool -> TEnv -> Ter -> IO (Either String Val)
runInfer debug lenv e = runTyping debug lenv (checkInfer e)

liftEval :: Eval a -> Typing a
liftEval = lift . lift

addC :: Ctxt -> (Tele,OEnv) -> [(Binder,Val)] -> Typing Ctxt
addC gam _             []          = return gam
addC gam ((y,a):as,nu) ((x,u):xus) = do
  v <- liftEval $ eval nu a
  addC ((x,v):gam) (as,oPair nu (y,u)) xus

-- Extract the type of a label as a closure
getLblType :: String -> Val -> Typing (Tele, OEnv)
getLblType c (Ter (Sum _ cas) r) = case getIdent c cas of
  Just as -> return (as,r)
  Nothing -> throwError ("getLblType " ++ show c)
getLblType c u = throwError ("expected a data type for the constructor "
                             ++ c ++ " but got " ++ show u)

-- Environment for type checker
data TEnv = TEnv { index   :: Int   -- for de Bruijn levels
                 , oenv     :: OEnv
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

addType :: (Binder,Ter) -> TEnv -> Typing TEnv
addType (x,a) tenv@(TEnv _ rho _ _) = do
  v <- liftEval $ eval rho a
  return $ addTypeVal (x,v) tenv

addBranch :: [(Binder,Val)] -> (Tele,OEnv) -> TEnv -> Typing TEnv
addBranch nvs (tele,env) (TEnv k rho gam v) = do
  e <- addC gam (tele,env) nvs
  return $ TEnv (k + length nvs) (upds rho nvs) e v

addDecls :: ODecls -> TEnv -> Typing TEnv
addDecls od@(ODecls d) (TEnv k rho gam v) = do
  let rho1 = oPDef True od rho
  es'  <- liftEval $ evals rho1 (declDefs d)
  gam' <- addC gam (declTele d,rho) es'
  return $ TEnv k rho1 gam' v
addDecls od tenv = return $ tenv {oenv = oPDef True od (oenv tenv)}

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

getFresh :: Typing Val
getFresh = do
    k <- index <$> ask
    e <- oenv <$> ask
    return $ mkVar k (support e)

checkDecls :: ODecls -> Typing ()
checkDecls (ODecls d) = do
  let (idents, tele, ters) = (declIdents d, declTele d, declTers d)
  trace ("Checking definition: " ++ unwords idents)
  checkTele tele
  rho <- oenv <$> ask
  localM (addTele tele) $ checks (tele,rho) ters
checkDecls _ = return ()

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
    if sort (map fst ces) == sort [n | ((n,_),_) <- cas]
       then sequence_ [ checkBranch (as,nu) f brc
                      | (brc, (_,as)) <- zip ces cas ]
       else throwError "case branches does not match the data type"
  (VPi a f,Lam x t)  -> do
    var <- getFresh
    local (addTypeVal (x,a)) $ checkM (liftEval (app f var)) t
  (VSigma a f, SPair t1 t2) -> do
    check a t1
    e <- oenv <$> ask
    v <- liftEval $ eval e t1
    checkM (liftEval (app f v)) t2
  (_,Where e d) -> do
    checkDecls d
    localM (addDecls d) $ check a e
  (_,PN _) -> return ()
  _ -> do
    v <- checkInfer t
    k <- index <$> ask
    b <- liftEval $ conv k v a
    unless b $
      throwError $ "check conv: " ++ show v ++ " /= " ++ show a

checkBranch :: (Tele,OEnv) -> Val -> Brc -> Typing ()
checkBranch (xas,nu) f (c,(xs,e)) = do
  k     <- index <$> ask
  env   <- oenv <$> ask
  let d  = support env
      l  = length xas
      us = map (`mkVar` d) [k..k+l-1]
  localM (addBranch (zip xs us) (xas,nu))
    $ checkM (liftEval (app f (VCon c us))) e

checkInfer :: Ter -> Typing Val
checkInfer e = case e of
  U -> return VU                 -- U : U
  Var n -> do
    gam <- ctxt <$> ask
    case getIdent n gam of
      Just v  -> return v
      Nothing -> throwError $ show n ++ " is not declared!"
  App t u -> do
    c <- checkInfer t
    case c of
      VPi a f -> do
        check a u
        rho <- oenv <$> ask
        v   <- liftEval $ eval rho u
        liftEval $ app f v
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
        e <- oenv <$> ask
        v <- liftEval $ eval e t
        liftEval $ app f (fstSVal v)
      _          -> throwError $ show c ++ " is not a sigma-type"
  Where t d -> do
    checkDecls d
    localM (addDecls d) $ checkInfer t
  _ -> throwError ("checkInfer " ++ show e)

checks :: (Tele,OEnv) -> [Ter] -> Typing ()
checks _              []     = return ()
checks ((x,a):xas,nu) (e:es) = do
  v   <- liftEval $ eval nu a
  check v e
  rho <- oenv <$> ask
  v'  <- liftEval $ eval rho e
  checks (xas,oPair nu (x,v')) es
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
