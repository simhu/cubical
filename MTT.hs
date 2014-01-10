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

import qualified CTT as C
import Eval

type Val = C.Val

type Label  = String

-- Branch of the form: c x1 .. xn -> e
type Brc    = (Label,([String],Exp))

-- Telescope (x1 : A1) .. (xn : An)
type Tele   = [(String,Exp)]

-- Labelled sum: c (x1 : A1) .. (xn : An)
type LblSum = [(Label,Tele)]

-- Context gives type values to identifiers
type Ctxt = [(String,Val)]

-- Mutual recursive definitions: (x1 : A1) .. (xn : An) and x1 = e1 .. xn = en
type Def = (Tele,[(String,Exp)])

-- -- De Bruijn levels
-- mkVar :: Int -> Exp
-- mkVar k = Var (genName k)

genName :: Int -> String
genName n = 'X' : show n

data Exp = App Exp Exp
         | Pi Exp Exp
         | Lam String Exp
         | Def Exp Def
         | Var String
         | U
         | Con String [Exp]
         | Fun C.Prim [Brc]
         | Sum C.Prim LblSum
         | Undef C.Prim
  deriving (Eq)

instance Show Exp where
 show = showExp

-- data Env = Empty
--          | Pair Env (String,Val)
--          | PDef Def Env         -- for handling recursive definitions,
--                                 -- see getE
--   deriving (Eq)

-- instance Show Env where
--   show = showEnv

-- For an expression t, returns (u,ts) where u is no application
-- and t = u ts
unApps :: Exp -> (Exp,[Exp])
unApps (App r s) = let (t,ts) = unApps r in (t, ts ++ [s])
unApps t         = (t,[])

apps :: C.Ter -> [C.Ter] -> C.Ter
apps = foldl C.App

lams :: [String] -> C.Ter -> C.Ter
lams bs t = foldr C.Lam t bs

translate :: Exp -> C.Ter
translate U              = C.U
translate (Undef prim)   = C.Undef prim
translate (Lam x t)      = C.Lam x $ translate t
translate (Pi a f)       = C.Pi (translate a) (translate f)
translate t@(App _ _)    =
  let (hd,rest) = unApps t
  in case hd of
    Var n | n `elem` reservedNames -> translatePrimitive n rest
    _ -> apps (translate hd) (map translate rest)
translate (Def e (_,ts)) = -- ignores types for now
  C.Where (translate e) [(n, translate e') | (n,e') <- ts]
translate (Var n) | n `elem` reservedNames = translatePrimitive n []
                  | otherwise              = C.Var n
translate (Con n ts)     = C.Con n $ map translate ts
translate (Fun pr bs)    =
  C.Branch pr [(n,(ns,translate b)) | (n,(ns,b)) <- bs]
translate (Sum pr lbs)   =
  C.LSum   pr [(n, [(n',translate e') | (n',e') <- tl]) | (n,tl) <- lbs]
-- translate t              = error $ "translate: can not handle " ++ show t

-- Gets a name for a primitive notion, a list of arguments which might be too
-- long and returns the corresponding concept in the internal syntax. Applies
-- the rest of the terms if the list of terms is longer than the arity.
translatePrimitive :: String -> [Exp] -> C.Ter
translatePrimitive n ts = case lookup n primHandle of
  Just (arity,_) | length ts < arity ->
    let r       = arity - length ts
        binders = map (\n -> '_' : show n) [1..r]
        vars    = map Var binders
    in lams binders $ translatePrimitive n (ts ++ vars)
  Just (arity,handler)               ->
    let (args,rest) = splitAt arity ts
    in apps (handler args) (map translate rest)
  Nothing                            ->
    error ("unknown primitive: " ++ show n)

-- | Primitive notions

-- name, (arity for Exp, handler)
type PrimHandle = [(String, (Int, [Exp] -> C.Ter))]

primHandle :: PrimHandle
primHandle =
  [ ("Id",            (3, primId))
  , ("refl",          (2, primRefl))
  , ("funExt",        (5, primExt))
  , ("J",             (6, primJ))
  , ("Jeq",           (4, primJeq))
  , ("inh",           (1, primInh))
  , ("inc",           (2, primInc))
  , ("squash",        (3, primSquash))
  , ("inhrec",        (5, primInhRec))
  , ("equivEq",       (5, primEquivEq))
  , ("transport",     (4, primTransport))
  , ("transportRef",  (2, primTransportRef))
  , ("equivEqRef",    (3, primEquivEqRef))
  , ("transpEquivEq", (6, primTransUEquivEq))
  , ("mapOnPath",     (6, primMapOnPath))
    -- TODO: Remove, this is just a temporary fix to solve a bug
    --  , ("subst",         (6, primSubst))
  ]

reservedNames :: [String]
reservedNames = map fst primHandle

primId :: [Exp] -> C.Ter
primId [a,x,y] = C.Id (translate a) (translate x) (translate y)

primRefl :: [Exp] -> C.Ter
primRefl [a,x] = C.Refl (translate x)

primExt :: [Exp] -> C.Ter
primExt [a,b,f,g,ptwise] =
  C.Ext (translate b) (translate f) (translate g) (translate ptwise)

primJ :: [Exp] -> C.Ter
primJ [a,u,c,w,v,p] =
  C.J (translate a) (translate u) (translate c)
        (translate w) (translate v) (translate p)

primJeq :: [Exp] -> C.Ter
primJeq [a,u,c,w] =
  C.JEq (translate a) (translate u) (translate c) (translate w)

primInh :: [Exp] -> C.Ter
primInh [a] = C.Inh (translate a)

primInc :: [Exp] -> C.Ter
primInc [a,x] = C.Inc (translate x)

primSquash :: [Exp] -> C.Ter
primSquash [a,x,y] = C.Squash (translate x) (translate y)

primInhRec :: [Exp] -> C.Ter
primInhRec [a,b,p,f,x] =
  C.InhRec (translate b) (translate p) (translate f) (translate x)

primEquivEq :: [Exp] -> C.Ter
primEquivEq [a,b,f,s,t] =
  C.EquivEq (translate a) (translate b) (translate f)
              (translate s) (translate t)

primTransport :: [Exp] -> C.Ter
primTransport [a,b,p,x] = C.TransU (translate p) (translate x)

primTransportRef :: [Exp] -> C.Ter
primTransportRef [a,x] = C.TransURef (translate x)

primEquivEqRef :: [Exp] -> C.Ter
primEquivEqRef [a,s,t] = C.EquivEqRef (translate a) (translate s) (translate t)

primTransUEquivEq :: [Exp] -> C.Ter
primTransUEquivEq [a,b,f,s,t,x] =
  C.TransUEquivEq (translate a) (translate b) (translate f)
                    (translate s) (translate t) (translate x)

primMapOnPath :: [Exp] -> C.Ter
primMapOnPath [ta,tb,f,a,b,p] =
  C.MapOnPath (translate f) (translate p)


-- TODO: remove
primSubst :: [Exp] -> C.Ter
primSubst [a,c,x,y,eq,p] =
  C.Trans (translate c) (translate eq) (translate p)

showExp :: Exp -> String
showExp1 :: Exp -> String

showExps :: [Exp] -> String
showExps = hcat . map showExp1

showExp1 U = "U"
showExp1 (Con c []) = c
showExp1 (Var x) = x
showExp1 u@(Fun {}) = showExp u
showExp1 u@(Sum {}) = showExp u
showExp1 u@(Undef {}) = showExp u
showExp1 u = parens $ showExp u

-- showEnv :: Env -> String
-- showEnv Empty            = ""
-- showEnv (Pair env (x,u)) = parens $ showEnv1 env ++ show u
-- showEnv (PDef xas env)   = showEnv env

-- showEnv1 Empty            = ""
-- showEnv1 (Pair env (x,u)) = showEnv1 env ++ C.showVal u ++ ", "
-- showEnv1 (PDef xas env)   = showEnv env


showExp e = case e of
 App e0 e1 -> showExp e0 <+> showExp1 e1
 Pi e0 e1 -> "Pi" <+> showExps [e0,e1]
 Lam x e -> "\\" ++ x ++ "->" <+> showExp e
 Def e d -> showExp e <+> "where" <+> showDef d
 Var x -> x
 U -> "U"
 Con c es -> c <+> showExps es
 Fun (n,str) _ -> str ++ show n
 Sum (_,str) _ -> str
 Undef (n,str) -> str ++ show n

showDef :: Def -> String
showDef (_,xts) = ccat (map (\(x,t) -> x <+> "=" <+> showExp t) xts)

lets :: [Def] -> Exp -> Exp
lets []     e = e
lets (d:ds) e = Def (lets ds e) d

upds :: C.Env -> [(String,Val)] -> C.Env
upds = foldl C.Pair

-- getE :: String -> C.Env -> Val
-- getE x (C.Pair _ (y,u)) | x == y = u
-- getE x (C.Pair s _)              = getE x s
-- getE x r@(C.PDef d r1)           = getE x (upds r1 (evals (snd d) r))

type TeleTer   = [(C.Binder,C.Ter)]

addC :: Ctxt -> (TeleTer,C.Env) -> [(String,Val)] -> Ctxt
addC gam _             []          = gam
addC gam ((y,a):as,nu) ((x,u):xus) =
  addC ((x,eval nu a):gam) (as,C.Pair nu (y,u)) xus

-- Extract the type of a label as a closure
getLblType :: String -> Val -> Typing (TeleTer, C.Env)
getLblType c (C.Ter (C.LSum _ cas) r) = case lookup c cas of
  Just as -> return (as,r)
  Nothing -> throwError ("getLblType " ++ show c)
getLblType c u = throwError ("expected a data type for the constructor "
                             ++ c ++ " but got " ++ show u)

-- Environment for type checker
data TEnv = TEnv { index :: Int   -- for de Bruijn levels
                 , env   :: C.Env
                 , ctxt  :: Ctxt }
          deriving Eq

tEmpty :: TEnv
tEmpty = TEnv 0 C.Empty []

-- Type checking monad
type Typing a = ReaderT TEnv (ErrorT String Identity) a

runTyping :: Typing a -> TEnv -> ErrorT String Identity a
runTyping = runReaderT

-- Used in the interaction loop
runDef :: TEnv -> Def -> Either String TEnv
runDef lenv d = do
  runIdentity $ runErrorT $ runTyping (checkDef d) lenv
  return $ addDef d lenv

runDefs :: TEnv -> [Def] -> Either String TEnv
runDefs = foldM runDef

runInfer :: TEnv -> Exp -> Either String Val
runInfer lenv e = runIdentity $ runErrorT $ runTyping (checkInfer e) lenv

addTypeVal :: (String,Val) -> TEnv -> TEnv
addTypeVal p@(x,_) (TEnv k rho gam) =
  TEnv (k+1) (C.Pair rho (x,mkVar k (C.support rho))) (p:gam)

addType :: (String,Exp) -> TEnv -> TEnv
addType (x,a) tenv@(TEnv _ rho _) = addTypeVal (x,eval rho (translate a)) tenv

addBranch :: [(String,Val)] -> (TeleTer,C.Env) -> TEnv -> TEnv
addBranch nvs (tele,env) (TEnv k rho gam) =
  TEnv (k + length nvs) (upds rho nvs) (addC gam (tele,env) nvs)

translateTele :: Tele -> TeleTer
translateTele ts = [(x,translate t) | (x,t) <- ts]

addDef :: Def -> TEnv -> TEnv
addDef d@(ts,es) (TEnv k rho gam) =
  let rho1 = C.PDef (translateTele es) rho
  in TEnv k rho1 (addC gam (translateTele ts,rho)
                 (evals rho1 (translateTele es)))

addTele :: Tele -> TEnv -> TEnv
addTele xas lenv = foldl (flip addType) lenv xas

getIndex :: Typing Int
getIndex = index <$> ask

getFresh :: Typing C.Val
getFresh = do
    e <- getEnv
    k <- getIndex
    return $ mkVar k (C.support e)

getEnv :: Typing C.Env
getEnv = env <$> ask

getCtxt :: Typing Ctxt
getCtxt = ctxt <$> ask

(=?=) :: Typing Exp -> Exp -> Typing ()
m =?= s2 = do
  s1 <- m
  unless (s1 == s2) $ throwError (show s1 ++ " =/= " ++ show s2)

checkDef :: Def -> Typing ()
checkDef (xas,xes) = trace ("checking definition " ++ show (map fst xes)) $ do
  checkTele xas
  rho <- getEnv
  local (addTele xas) $ checks (translateTele xas,rho) (map snd xes)

checkTele :: Tele -> Typing ()
checkTele []          = return ()
checkTele ((x,a):xas) = do
  check C.VU a
  local (addType (x,a)) $ checkTele xas

check :: Val -> Exp -> Typing ()
check a t = case (a,t) of
  (_,Con c es) -> do
    (bs,nu) <- getLblType c a
    checks (bs,nu) es
  (C.VU,Pi a (Lam x b)) -> do
    check C.VU a
    local (addType (x,a)) $ check C.VU b
  (C.VU,Sum _ bs) -> sequence_ [checkTele as | (_,as) <- bs]
  (C.VPi (C.Ter (C.LSum _ cas) nu) f,Fun _ ces) ->
    if map fst ces == map fst cas
       then sequence_ [ checkBranch (as,nu) f brc
                      | (brc, (_,as)) <- zip ces cas ]
       else throwError "case branches does not match the data type"
  (C.VPi a f,Lam x t)  -> do
    var <- getFresh
    local (addTypeVal (x,a)) $ check (app f var) t
  (_,Def e d) -> do
    checkDef d
    local (addDef d) $ check a e
  (_,Undef _) -> return ()
  _ -> do
    v <- checkInfer t
    k <- getIndex
    if conv k v a then return ()
    else throwError $ "check conv: " ++ show v ++ " /= " ++ show a

checkBranch :: (TeleTer,C.Env) -> Val -> Brc -> Typing ()
checkBranch (xas,nu) f (c,(xs,e)) = do
  k     <- getIndex
  env   <- getEnv
  let d  = C.support env
  let l  = length xas
  let us = map (flip mkVar d) [k..k+l-1]
  local (addBranch (zip xs us) (xas,nu)) $ check (app f (C.VCon c us)) e

checkInfer :: Exp -> Typing Val
checkInfer e = case e of
  U -> return C.VU                 -- U : U
  Var n -> do
    gam <- getCtxt
    case lookup n gam of
      Just v  -> return v
      Nothing -> throwError $ show n ++ " is not declared!"
  App t u -> do
    c <- checkInfer t
    case c of
      C.VPi a f -> do
        check a u
        rho <- getEnv
        return (app f (eval rho (translate u)))
      _      ->  throwError $ show c ++ " is not a product"
  Def t d -> do
    checkDef d
    local (addDef d) $ checkInfer t
  _ -> throwError ("checkInfer " ++ show e)

checks :: (TeleTer,C.Env) -> [Exp] -> Typing ()
checks _              []     = return ()
checks ((x,a):xas,nu) (e:es) = do
  check (eval nu a) e
  rho <- getEnv
  checks (xas,C.Pair nu (x,eval rho (translate e))) es
checks _              _      = throwError "checks"

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

-- a show function

