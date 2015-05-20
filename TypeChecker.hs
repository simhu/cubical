{-# LANGUAGE PatternSynonyms #-}
module TypeChecker where

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

-- Type checking monad
type Typing a = ReaderT TEnv (ErrorT String IO) a

-- Environment for type checker
data TEnv = TEnv { index   :: Int   -- for de Bruijn levels
                 , env     :: Env
                 , ctxt    :: Ctxt
                 , verbose :: Bool  -- Should it be verbose and print
                                    -- what it typechecks?
                 }
  deriving (Show)

verboseEnv, silentEnv :: TEnv
verboseEnv = TEnv 0 Empty [] True
silentEnv  = TEnv 0 Empty [] False

addCol :: Binder -> CVal -> TEnv -> TEnv
addCol x p (TEnv k rho gam v) = TEnv (k+1) (PCol rho (x,p)) gam v

addTypeVal p@(x,_) (TEnv k rho gam v) =
  TEnv (k+1) (Pair rho (x,mkVar k)) (p:gam) v

addType :: (Binder,Ter) -> TEnv -> Typing TEnv
addType (x,a) tenv@(TEnv _ rho _ _) = return $ addTypeVal (x,eval rho a) tenv

addC :: Ctxt -> (Tele,Env) -> [(Binder,Val)] -> Typing Ctxt
addC gam _             []          = return gam
addC gam ((y,a):as,nu) ((x,u):xus) = 
  addC ((x,eval nu a):gam) (as,Pair nu (y,u)) xus

addBranch :: [(Binder,Val)] -> (Tele,Env) -> TEnv -> Typing TEnv
addBranch nvs (tele,env) (TEnv k rho gam v) = do
  e <- addC gam (tele,env) nvs
  return $ TEnv (k + length nvs) (upds rho nvs) e v

addDecls :: Decls -> TEnv -> Typing TEnv
addDecls d (TEnv k rho gam v) = do
  let rho1 = PDef [ (x,y) | (x,_,y) <- d ] rho
      es' = evals rho1 (declDefs d)
  gam' <- addC gam (declTele d,rho) es'
  return $ TEnv k rho1 gam' v

addTele :: Tele -> TEnv -> Typing TEnv
addTele xas lenv = foldM (flip addType) lenv xas

trace :: String -> Typing ()
trace s = do
  b <- verbose <$> ask
  when b $ liftIO (putStrLn s)

runTyping :: TEnv -> Typing a -> IO (Either String a)
runTyping env t = runErrorT $ runReaderT t env

-- Used in the interaction loop
runDecls :: TEnv -> Decls -> IO (Either String TEnv)
runDecls tenv d = runTyping tenv $ do
  checkDecls d
  addDecls d tenv

runDeclss :: TEnv -> [Decls] -> IO (Maybe String,TEnv)
runDeclss tenv []         = return (Nothing, tenv)
runDeclss tenv (d:ds) = do
  x <- runDecls tenv d
  case x of
    Right tenv' -> runDeclss tenv' ds
    Left s      -> return (Just s, tenv)

runInfer :: TEnv -> Ter -> IO (Either String Val)
runInfer lenv e = runTyping lenv (checkInfer e)

-- Extract the type of a label as a closure
getLblType :: String -> Val -> Typing (Tele, Env)
getLblType c (Ter (Sum _ cas) r) = case getIdent c cas of
  Just as -> return (as,r)
  Nothing -> throwError ("getLblType " ++ show c)
getLblType c u = throwError ("expected a data type for the constructor "
                             ++ c ++ " but got " ++ show u)

-- Useful monadic versions of functions:
localM :: (TEnv -> Typing TEnv) -> Typing a -> Typing a
localM f r = do
  e <- ask
  a <- f e
  local (const a) r

getFresh :: Typing Val
getFresh = mkVar <$> index <$> ask

getFreshCol :: Typing CVal
getFreshCol = mkCol <$> index <$> ask

checkDecls :: Decls -> Typing ()
checkDecls d = do
  let (idents, tele, ters) = (declIdents d, declTele d, declTers d)
  trace ("Checking: " ++ unwords idents)
  checkTele tele
  rho <- asks env
  localM (addTele tele) $ checks (tele,rho) ters

checkTele :: Tele -> Typing ()
checkTele []          = return ()
checkTele ((x,a):xas) = do
  inferType a
  localM (addType (x,a)) $ checkTele xas

check :: Val -> Ter -> Typing ()
check a t = case (a,t) of
  (_,Constr _ t') -> check a t' -- FIXME: constraints
  (VConstr _ a',_) -> check a' t -- FIXME: constraints
  (_,Con c es) -> do
    (bs,nu) <- getLblType c a
    checks (bs,nu) es
  (VU,Sum _ bs) -> sequence_ [checkTele as | (_,as) <- bs]
  (VPi (Ter (Sum _ cas) nu) f,Split _ ces) -> do
    let cas' = sortBy (compare `on` fst . fst) cas
        ces' = sortBy (compare `on` fst) ces
    if map (fst . fst) cas' == map fst ces'
       then sequence_ [ checkBranch (as,nu) f brc
                      | (brc, (_,as)) <- zip ces' cas' ]
       else throwError "case branches does not match the data type"
  (VPi a f,Lam is x t)  -> do
    var <- getFresh
    rho <- asks env
    let is' = lkCols rho is
    local (addTypeVal (x,cpis is' a)) $ check (app f $ capps var is') t
  (VSigma a f, SPair t1 t2) -> do
    v <- checkEval a t1
    check (app f v) t2
  (VCPi f, CLam x t) -> do
    var <- getFreshCol
    local (addCol x var) $ check (capp f var) t
  (VCPi f,CPair a b) -> do
    a' <- checkEval (face f) a
    check (f `ni` a') b

    {-
   f : (x:A(i0)) -> B(i0)
   g : (x:forall i. A) -> <i> B(i) ? f (x@0)
----------------------------------------------
   <f,g> : forall i. (x:A) -> B
-}
  (VCPi f,Phi t u) -> do
    t' <- checkEval (face f) t
    p@(CVar i) <- getFreshCol
    case f `capp` p of
        VPi a f' -> do
          check (VPi (cpi i a) $ VLam $ \x -> ni (clam i (f' `app` (x `capp` p))) (t' `app` face x)) u
        _ -> throwError ";pqw[uftqf ]"
  (_,CApp u c) -> do
    c' <- colorEval c
    case c' of
      CVar i -> check (VCPi $ clam' $ \j -> ceval i j a) u
      _ -> do
        v <- checkInfer t
        checkConv "inferred type" a v
  (VNi f b,Psi b' p) | VV _ <- capp f (CVar $ Color "__NOPE__") -> do
    let x = noLoc n
        n = "__PSI_ARG__"
    inferType b'
    b'' <- eval' b'
    checkConv "ni" b b''
    local (addTypeVal (x,b)) $ inferType (App p $ Var n)
    return ()
  (VNi f b,Param p) -> do
    p' <- checkEval (VCPi f) p
    checkConv "param" (face p') b
  (_,Where e d) -> do
    checkDecls d
    localM (addDecls d) $ check a e
  (_,Undef _) -> return ()
  _ -> do
    v <- checkInfer t
    checkConv "inferred type" a v

colorEval :: CTer -> Typing CVal
colorEval c = do
  e <- asks env
  return $ colEval e c
  
checkEval :: Val -> Ter -> Typing Val
checkEval a t = do
  check a t
  eval' t

eval' :: Ter -> Typing Val
eval' t = do
  e <- asks env
  return $ eval e t

checkConv msg a v = do
    k <- index <$> ask
    case conv k v a of
      Nothing -> return ()
      Just err -> do
      rho <- asks env
      throwError $ msg ++ " check conv: \n  " ++ show v ++ " /= " ++ show a ++ "\n in environment" ++ show rho ++ "\n because  " ++ err

checkBranch :: (Tele,Env) -> Val -> Brc -> Typing ()
checkBranch (xas,nu) f (c,(xs,e)) = do
  k   <- asks index
  env <- asks env
  let l  = length xas
      us = map mkVar [k..k+l-1]
  localM (addBranch (zip xs us) (xas,nu)) $ check (app f (VCon c us)) e

inferType :: Ter -> Typing Val
inferType t = do
  a <- checkInfer t
  case a of
   VV _ -> return a
   _ -> throwError $ show a ++ " is not a type"

sortPlus :: Maybe [Color] -> CVal -> Maybe [Color]
sortPlus Nothing _ = Nothing
sortPlus (Just is) i = Just (catMax i ++ is)

checkInfer :: Ter -> Typing Val
checkInfer e = case e of
  CPi (CLam x t) -> do
    var <- getFreshCol
    local (addCol x var) $ inferType t
  CU _ -> eval <$> asks env <*> pure e
  Pi a (Lam is x b) -> do
    inferType a
    localM (addType (x,tcpis is a)) $ inferType b
  Sigma a (Lam [] x b) -> do
    inferType a
    localM (addType (x,a)) $ inferType b
  Constr _ t -> checkInfer t -- FIXME: constraints in the type
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
        rho <- asks env
        let v = eval rho u
        return $ app f v
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
        e <- asks env
        let v = eval e t
        return $ app f (fstSVal v)
      _          -> throwError $ show c ++ " is not a sigma-type"
  CApp t u -> do
    c <- checkInfer t
    u' <- colorEval u
    case c of
      VCPi f -> do return $ (capp f u')
      _          -> throwError $ show t ++ " is not a type family (1)"
  Param t -> do
    c <- checkInfer t
    rho <- asks env
    let v = eval rho t
    case c of
      VCPi f -> do return $ ni f (face v)
      _          -> throwError $ show t ++ " is not a type family (2)"
  Ni t u -> do
    t' <-checkEval (VCPi $ clam' $ \_ -> VU) t
    check (face t') u
    return VU
  Psi a p -> do
    VV sort <- inferType a
    a' <- eval' a
    check (VPi a' $ VLam $ \_ -> VU) p
    return $ (clam' $ \i -> VV (sortPlus sort i)) `ni` a'
  CPair a (Psi a' p) -> do
    check (VCPi $ clam' $ \_ -> VU) (CPair a (Psi a' p))
    return (VCPi $ clam' $ \_ -> VU)
  Where t d -> do
    checkDecls d
    localM (addDecls d) $ checkInfer t
  _ -> throwError ("checkInfer " ++ show e)

checks :: (Tele,Env) -> [Ter] -> Typing ()
checks _              []     = return ()
checks ((x,a):xas,nu) (e:es) = do
  let v = eval nu a
  check v e
  rho <- asks env
  let v' = eval rho e
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
