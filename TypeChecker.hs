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
import Control.Arrow hiding (app)
import Pretty

import CTT
import Eval

-- Type checking monad
type Typing a = ReaderT TEnv (ErrorT String IO) a

-- Environment for type checker
data TEnv = TEnv { index   :: Int   -- for de Bruijn levels
                 , env'    :: Env'
                 , verbose :: Bool  -- Should it be verbose and print
                                    -- what it typechecks?
                 }
  deriving (Eq,Show)

env :: TEnv -> Env
env = snd . env'

shift :: TEnv -> Integer
shift = fst . env'

verboseEnv, silentEnv :: TEnv
verboseEnv = TEnv 0 (0,Empty) True
silentEnv  = TEnv 0 (0,Empty) False

addVal :: (Binder,Val) -> TEnv -> TEnv
addVal (x,v) (TEnv k (n,rho) verb) =
  TEnv k (n,Pair rho (x,v)) verb

addValk :: (Binder,Val) -> TEnv -> TEnv
addValk (x,v) (TEnv k (n,rho) verb) =
  TEnv (k+1) (n,Pair rho (x,v)) verb
  
addTypeVal :: (Binder,Val) -> TEnv -> TEnv
addTypeVal (x,t) (TEnv k (n,rho) v) =
  TEnv (k+1) (n,Pair rho (x,mkVar k t)) v

-- todo : factorize addVal/addTypeVal

addType :: (Binder,Ter) -> TEnv -> Typing TEnv
addType (x,a) tenv@(TEnv _ (n,rho) _) =
  return $ addTypeVal (x,eval (n,rho) a) tenv

addDecls :: Decls -> TEnv -> TEnv
addDecls d (TEnv k (n,rho) v) = TEnv k (n,PDef [(x,(y,z)) | (x,y,z) <- d] rho) v

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
  return $ addDecls d tenv

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
getLblType :: String -> Val -> Typing (Tele, Env')
getLblType c (Ter (Sum _ cas) nr) = case getIdent c cas of
  Just as -> return (as,nr)
  Nothing -> throwError ("getLblType " ++ show c)
getLblType c u = throwError ("expected a data type for the constructor "
                             ++ c ++ " but got " ++ show u)

-- Useful monadic versions of functions:
localM :: (TEnv -> Typing TEnv) -> Typing a -> Typing a
localM f r = do
  e <- ask
  a <- f e
  local (const a) r

getFresh :: Val -> Typing Val
getFresh a = mkVar <$> asks index <*> pure a

checkTele :: Tele -> Typing ()
checkTele [] = return ()
checkTele ((x,a):xas) = do
  checkType a
  localM (addType (x,a)) (checkTele xas)

checkType :: Ter -> Typing ()
checkType t = case t of
  U _             -> return ()
  Pi a (Lam x b) -> do
    checkType a
    localM (addType (x,a)) (checkType b)
  Plus t -> do
    local (shiftTEnv 1) $ checkType t
  Minus t -> do
    rho <- asks env'
    (eval rho (Minus t)) `seq` local (shiftTEnv (-1)) $ checkType t
  _ -> do
    e <- checkInfer t
    case e of
      VU _ -> return ()
      _ -> throwError "checkType"

checkDecls :: Decls -> Typing ()
checkDecls d = do
  let (idents, tele, ters) = (declIdents d, declTele d, declTers d)
  trace ("Checking: " ++ unwords idents)
  checkTele tele
  rho <- asks env'
  localM (addTele tele) $ checks (tele,rho) ters

check :: Val -> Ter -> Typing ()
check a t = case (a,t) of
  (_,Con c es) -> do
    (bs,nu) <- getLblType c a
    checks (bs,nu) es
  (VU n,Pi a (Lam x b)) -> do
    check (VU n) a
    localM (addType (x,a)) $ check (VU n) b
  (VU n,Sigma a (Lam x b)) -> do
    check (VU n) a
    localM (addType (x,a)) $ check (VU n) b
  (VU n,Sum _ bs) -> sequence_ [checkTele as | (_,as) <- bs]
  (VPi (Ter (Sum _ cas) (n,nu)) f,Split _ ces) -> do
    let cas' = sortBy (compare `on` fst . fst) cas
        ces' = sortBy (compare `on` fst) ces
    if map (fst . fst) cas' == map fst ces'
       then sequence_ [ checkBranch (as,(n,nu)) f brc
                      | (brc, (_,as)) <- zip ces' cas' ]
       else throwError "case branches does not match the data type"
  (VPi a f,Lam x t)  -> do
    var <- getFresh a
    local (addTypeVal (x,a)) $ check (app f var) t
  (VSigma a f, SPair t1 t2) -> do
    check a t1
    e <- asks env'
    let v = eval e t1
    check (app f v) t2
  (_,Where e d) -> do
    checkDecls d
    local (addDecls d) $ check a e
  (_,Undef _) -> return ()
  _ -> do
    v <- checkInfer t
    k <- index <$> ask
    unless (subt k v a) $
      throwError $ "check subt: " ++ show v ++ " </= " ++ show a
  
addBranch :: [Binder] -> (Tele,Env') -> Typing [(Binder,Val)]
addBranch []      _                = return []
addBranch (x:xs) ((y,a):as,(n,nu)) = do
  k <- asks index
  let z = mkVar k (eval (n,nu) a)
  vs <- local (addValk (x,z)) $ addBranch xs (as,(n,Pair nu (y,z)))
  return $ (x,z):vs
  
-- todo: get rid of monads?

checkBranch :: (Tele,Env') -> Val -> Brc -> Typing ()
checkBranch (xas,(n,nu)) f (c,(xs,e)) = do
  vs <- addBranch xs (xas,(n,nu))
  local (\tenv -> foldr addVal tenv vs) $ check (app f (VCon c (map snd vs))) e

lookType :: Ident -> Env' -> Val
lookType x (k, e) = look' e
  where
    look' (Pair rho (n@(y,l),u))
      | x == y    = case u of
        VVar _ _ v -> v
        _          -> error "lookType: should be a VVar"
      | otherwise = look' rho
    look' r@(PDef es r1) = case lookupIdent x es of
      Just (y,(t,v))  -> eval (k,r) t
      Nothing       -> look' r1
    look' Empty   = error "lookType: unbound variable at type checking"

shiftTEnv :: Integer -> TEnv -> TEnv
shiftTEnv n (TEnv k (m,rho) verb) = TEnv k (n+m,rho) verb

checkInfer :: Ter -> Typing Val
checkInfer e = case e of
  U n -> do
    l <- asks shift
    return (VU (n+l+1))
  Var n -> do
    rho' <- asks env'
    return $ lookType n rho'
  App t u -> do
    c <- checkInfer t
    case c of
      VPi a f -> do
        check a u
        rho <- asks env'
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
        e <- asks env'
        let v = eval e t
        return $ app f (fstSVal v)
      _          -> throwError $ show c ++ " is not a sigma-type"
  Where t d -> do
    checkDecls d
    local (addDecls d) $ checkInfer t
  Plus t -> do
    local (shiftTEnv 1) $ checkInfer t
  Minus t -> do
    rho <- asks env'
    (eval rho (Minus t)) `seq` local (shiftTEnv (-1)) $ checkInfer t
  _ -> throwError ("checkInfer " ++ show e)

checks :: (Tele,Env') -> [Ter] -> Typing ()
checks _              []     = return ()
checks ((x,a):xas,(n,nu)) (e:es) = do
  let v = eval (n,nu) a
  check v e
  rho <- asks env'
  let v' = eval rho e
  checks (xas,(n,Pair nu (x,v'))) es
checks _              _      = throwError "checks"