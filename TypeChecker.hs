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
import Connections

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
getLblType :: String -> Val -> Typing (Tele, Env)
getLblType c (Ter (Sum _ cas) r) = case getIdent c cas of
  Just as -> return (as,r)
  Nothing -> throwError ("getLblType " ++ show c)
getLblType c (Ter (HSum _ hlabels) r) =
  let cas = map hLabelToBinderTele (filter isLabel hlabels)
  in case getIdent c cas of
    Just as -> return (as,r)
    Nothing -> throwError ("getLblType " ++ show c)
getLblType c u = throwError ("expected a data type for the constructor "
                             ++ c ++ " but got " ++ show u)

getHLblType :: String -> Val -> Typing (Tele, Env)
getHLblType c (Ter (HSum _ hlabels) r) =
  let cas = map hLabelToBinderTele hlabels
  in case getIdent c cas of
    Just as -> return (as,r)
    Nothing -> throwError ("getHLblType" <+> show c)
getHLblType c u = throwError ("expected a hdata type for the path constructor"
                             <+> c <+> "but got" <+> show u)


-- Environment for type checker
data TEnv = TEnv { index   :: Int   -- for de Bruijn levels
                 , env     :: Env
                 , ctxt    :: Ctxt
                 , verbose :: Bool  -- Should it be verbose and print
                                    -- what it typechecks?
                 }
  deriving (Eq,Show)

verboseEnv, silentEnv :: TEnv
verboseEnv = TEnv 0 Empty [] True
silentEnv  = TEnv 0 Empty [] False

addTypeVal :: (Binder,Val) -> TEnv -> TEnv
addTypeVal p@(x,_) (TEnv k rho gam v) =
  TEnv (k+1) (Pair rho (x,mkVar k)) (p:gam) v

-- addTypeVals :: [(Binder,Val)] -> TEnv -> TEnv
-- addTypeVals = flip $ foldl (flip addTypeVal)

addType :: (Binder,Ter) -> TEnv -> TEnv
addType (x,a) tenv@(TEnv _ rho _ _) = addTypeVal (x,eval rho a) tenv

addC :: Ctxt -> (Tele,Env) -> [(Binder,Val)] -> Ctxt
addC gam _             []          = gam
addC gam ((y,a):as,nu) ((x,u):xus) =
  let v = eval nu a
  in addC ((x,v):gam) (as,Pair nu (y,u)) xus

addBranch :: [(Binder,Val)] -> (Tele,Env) -> TEnv -> TEnv
addBranch nvs (tele,env) (TEnv k rho gam v) =
  let e = addC gam (tele,env) nvs
  in TEnv (k + length nvs) (upds rho nvs) e v

addDecls :: Decls -> TEnv -> TEnv
addDecls d (TEnv k rho gam v) =
  let rho1 = PDef (declDefs d) rho
      -- es'  = evals rho1 (declDefs d)
      -- gam' = addC gam (declTele d,rho) es'
      gam' = gam ++ [(x,eval rho1 a) | (x,a) <- declTele d]
  in TEnv k rho1 gam' v

addTele :: Tele -> TEnv -> TEnv
addTele xas lenv = foldl (flip addType) lenv xas

getFresh :: Typing Val
getFresh = mkVar <$> asks index

checkDecls :: Decls -> Typing ()
checkDecls d = do
  let (idents, tele, ters) = (declIdents d, declTele d, declTers d)
  trace ("Checking: " ++ unwords idents)
  checkTele tele
  -- rho <- asks env
  -- local (addTele tele) $ checks (tele,rho) ters
  local (addDecls d) $ do
    rho <- asks env
    checks (tele,rho) ters

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
       else throwError "case branches do not match the data type"
  (VPi a f,Lam x t)  -> do
    var <- getFresh
    local (addTypeVal (x,a)) $ check (app f var) t
  (VSigma a f, SPair t1 t2) -> do
    check a t1
    e <- asks env
    check (app f (eval e t1)) t2
  (VId (Path i u) v0 v1,PCon c es _ t0 t1) -> do -- TODO: what about the <i> ?
    (bs,nu) <- getHLblType c u
    checks (bs,nu) es
    k   <- asks index
    rho <- asks env
    let env' = upds nu (evals rho (zip (map fst bs) es))
        w0   = eval env' t0
        w1   = eval env' t1
    if conv k v0 w0
      then unless (conv k v1 w1)
           (throwError $ "check conv pcon:" <+> show v1 <+> "/=" <+> show w1)
      else throwError $ "check conv pcon:" <+> show v0 <+> "/=" <+> show w0
  (VU,HSum _ hlabels) -> forM_ hlabels $ \hlabel -> case hlabel of
    Label _ tele -> checkTele tele
    HLabel n tele t0 t1 -> do
      checkTele tele
      rho <- asks env
      k   <- asks index
      let l  = length tele
          us = map mkVar [k..k+l-1]
          e  = eval rho t
      local (addBranch (zip (map fst tele) us) (tele,rho)) $ do
        check e t0
        check e t1
  (VPi hs@(Ter (HSum _ hlabels) nu) f,HSplit _ f' hbranches) -> do
    k   <- asks index
    rho <- asks env
    unless (conv k f (eval rho f'))
      (throwError "check HSplit: families don't match")
    let hlabels'   = sortBy (compare `on` fst . hLabelToBinder) hlabels
        hbranches' = sortBy (compare `on` hBranchToLabel) hbranches
    if map (fst . hLabelToBinder) hlabels' == map hBranchToLabel hbranches'
      then sequence_ [ checkHBranch (hl,nu) f hbr (eval rho t)
                     | (hbr,hl) <- zip hbranches' hlabels']
      else throwError "hsplit branches do not match the hdata type"
  (_,Where e d) -> do
    checkDecls d
    local (addDecls d) $ check a e
  (_,PN _) -> return ()
  _ -> do
    v <- checkInfer t
    k <- asks index
    unless (conv k v a) $
      throwError $ "check conv: " ++ show v ++ " /= " ++ show a


checkBranch :: (Tele,Env) -> Val -> Brc -> Typing ()
checkBranch (xas,nu) f (c,(xs,e)) = do
  k   <- asks index
  rho <- asks env
  let d  = support rho
      l  = length xas
      us = map mkVar [k..k+l-1]
  local (addBranch (zip xs us) (xas,nu)) $ check (app f (VCon c us)) e

checkHBranch :: (HLabel,Env) -> Val -> HBranch -> Val -> Typing ()
checkHBranch (Label _ tele,nu) f (Branch c binders e) _ =
  checkBranch (tele,nu) f (c,(binders,e))
checkHBranch (HLabel _ tele t0 t1,nu) f (HBranch c binders e) hsplit = do
  k   <- asks index
  rho <- asks env
  let l    = length tele
      us   = map mkVar [k..k+l-1]
      rho' = upds nu (zip (map fst tele) us)
      u0   = app hsplit (eval rho' t0)
      u1   = app hsplit (eval rho' t1)
  local (addBranch (zip binders us) (tele,nu)) $ do
    rho'' <- asks env
    let tpc = PCon c (map Var (map fst binders)) (map fst binders) t0 t1
        pc  = eval rho'' tpc
        i   = fresh (f,rho'',u0,u1)
    check (VId (Path i $ app f (pc @@ i)) u0 u1) e
checkHBranch (hlb,_) _ hbr _ =
  throwError ("checkHBranch: constructor kinds don't match up in"
             <+> show hlb <+> "and" <+> show hbr)


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
        rho <- asks env
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
        e <- asks env
        return $ app f (fstSVal (eval e t))
      _          -> throwError $ show c ++ " is not a sigma-type"
  Where t d -> do
    checkDecls d
    local (addDecls d) $ checkInfer t
  _ -> throwError ("checkInfer " ++ show e)

checks :: (Tele,Env) -> [Ter] -> Typing ()
checks _              []     = return ()
checks ((x,a):xas,nu) (e:es) = do
  check (eval nu a) e
  rho <- asks env
  checks (xas,Pair nu (x,eval rho e)) es
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
