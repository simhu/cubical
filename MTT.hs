-- miniTT, with recursive definitions
module MTT where

import Data.Either
import Data.List
import Data.Maybe
import Control.Monad
import Debug.Trace
import Control.Monad.Trans.Error hiding (throwError)
import Control.Monad.Trans.Reader
import Control.Monad.Identity
import Control.Monad.Error (throwError)
import Control.Applicative
import Pretty

import CTT
import Eval

genName :: Int -> String
genName n = 'X' : show n

addC :: Ctxt -> (Tele,OEnv) -> [(String,Val)] -> Ctxt
addC gam _             []          = gam
addC gam ((y,a):as,nu) ((x,u):xus) =
  addC ((x,eval nu a):gam) (as,oPair nu (y,u)) xus

-- Extract the type of a label as a closure
getLblType :: String -> Val -> Typing (Tele, OEnv)
getLblType c (Ter (Sum _ cas) r) = case lookup c cas of
  Just as -> return (as,r)
  Nothing -> throwError ("getLblType " ++ show c)
getLblType c u = throwError ("expected a data type for the constructor "
                             ++ c ++ " but got " ++ show u)

-- Environment for type checker
data TEnv = TEnv { index   :: Int   -- for de Bruijn levels
                 , oenv    :: OEnv
                 , ctxt    :: Ctxt} -- opaque definitions
          deriving Eq

tEmpty :: TEnv
tEmpty = TEnv 0 (OEnv Empty []) []

-- Type checking monad
type Typing a = ReaderT TEnv (ErrorT String Identity) a

runTyping :: Typing a -> TEnv -> ErrorT String Identity a
runTyping = runReaderT

-- Used in the interaction loop
runDef :: TEnv -> ODef -> Either String TEnv
runDef tenv (ODef d)    = do
  runIdentity $ runErrorT $ runTyping (checkDef d) tenv
  return $ addDef d tenv
runDef tenv op         = return $ tenv {oenv = oenv'}
  where OEnv env opaques = oenv tenv
        oenv' = OEnv env $ case op of
          Opaque n      -> n : opaques
          Transparent n -> n `delete` opaques

runDefs :: TEnv -> [ODef] -> Either String TEnv
runDefs = foldM runDef

runInfer :: TEnv -> Ter -> Either String Val
runInfer lenv e = runIdentity $ runErrorT $ runTyping (checkInfer e) lenv

addTypeVal :: (String,Val) -> TEnv -> TEnv
addTypeVal p@(x,_) (TEnv k rho gam) =
  TEnv (k+1) (oPair rho (x,mkVar k (support rho))) (p:gam)

addType :: (String,Ter) -> TEnv -> TEnv
addType (x,a) tenv@(TEnv _ rho _) =
  addTypeVal (x,eval rho a) tenv

addBranch :: [(String,Val)] -> (Tele,OEnv) -> TEnv -> TEnv
addBranch nvs (tele,env) (TEnv k rho gam) =
  TEnv (k + length nvs) (upds rho nvs) (addC gam (tele,env) nvs)

addDef :: Def -> TEnv -> TEnv
addDef d@(ts,es) (TEnv k rho gam) =
  let rho1 = oPDef es rho
  in TEnv k rho1 (addC gam (ts, rho) (evals rho1 es))

addTele :: Tele -> TEnv -> TEnv
addTele xas lenv = foldl (flip addType) lenv xas

getIndex :: Typing Int
getIndex = index <$> ask

getFresh :: Typing Val
getFresh = do
    k <- getIndex
    e <- getOEnv
    return $ mkVar k (support e)

getOEnv :: Typing OEnv
getOEnv = oenv <$> ask

getCtxt :: Typing Ctxt
getCtxt = ctxt <$> ask

(=?=) :: Typing Ter -> Ter -> Typing ()
m =?= s2 = do
  s1 <- m
  unless (s1 == s2) $ throwError (show s1 ++ " =/= " ++ show s2)

checkDef :: Def -> Typing ()
checkDef (xas,xes) = trace ("checking definition " ++ show (map fst xes)) $ do
  checkTele xas
  rho <- getOEnv
  local (addTele xas) $ checks (xas,rho) (map snd xes)

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
  (VU,Sum _ bs) -> sequence_ [checkTele as | (_,as) <- bs]
  (VPi (Ter (Sum _ cas) nu) f,Split _ ces) ->
    if map fst ces == map fst cas
       then sequence_ [ checkBranch (as,nu) f brc
                      | (brc, (_,as)) <- zip ces cas ]
       else throwError "case branches does not match the data type"
  (VPi a f,Lam x t)  -> do
    var <- getFresh
    local (addTypeVal (x,a)) $ check (app f var) t
  (_,Where e d) -> do
    checkDef d
    local (addDef d) $ check a e
  (_,PN _) -> return ()
  _ -> do
    v <- checkInfer t
    k <- getIndex
    if conv k v a then return ()
    else throwError $ "check conv: " ++ show v ++ " /= " ++ show a

checkBranch :: (Tele,OEnv) -> Val -> Brc -> Typing ()
checkBranch (xas,nu) f (c,(xs,e)) = do
  k     <- getIndex
  env   <- getOEnv
  let d  = support env
  let l  = length xas
  let us = map (`mkVar` d) [k..k+l-1]
  local (addBranch (zip xs us) (xas,nu)) $ check (app f (VCon c us)) e

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
        rho <- getOEnv
        return (app f (eval rho u))
      _      ->  throwError $ show c ++ " is not a product"
  Where t d -> do
    checkDef d
    local (addDef d) $ checkInfer t
  _ -> throwError ("checkInfer " ++ show e)

checks :: (Tele,OEnv) -> [Ter] -> Typing ()
checks _              []     = return ()
checks ((x,a):xas,nu) (e:es) = do
  check (eval nu a) e
  rho <- getOEnv
  checks (xas,oPair nu (x,eval rho e)) es
checks _              _      = throwError "checks"

-- Not used since we have U : U
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
