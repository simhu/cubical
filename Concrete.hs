{-# LANGUAGE TupleSections #-}

-- Convert the concrete syntax into the syntax of miniTT.
module Concrete where

import Exp.Abs
import qualified MTT as A

import Control.Arrow
import Control.Applicative
import Control.Monad.Trans
import Control.Monad.Trans.State
import Control.Monad.Trans.Reader
import Control.Monad.Trans.Error hiding (throwError)
import Control.Monad.Error (throwError)
import Control.Monad
import Data.Functor.Identity
import Data.Function
import Data.Graph
import Data.List
import Data.Maybe

type Tele = [VDecl]

-- | Useful auxiliary functions
unions :: Eq a => [[a]] -> [a]
unions = foldr union []

-- Applicative cons
(<:>) :: Applicative f => f a -> f [a] -> f [a]
a <:> b = (:) <$> a <*> b

-- un-something functions
unIdent :: AIdent -> String
unIdent (AIdent (_,n)) = n

unArg :: Arg -> String
unArg (Arg n) = unIdent n
unArg NoArg   = "_"

unArgs :: [Arg] -> [String]
unArgs = map unArg

unBinder :: Binder -> Arg
unBinder (Binder b) = b

unArgBinder :: Binder -> String
unArgBinder = unArg . unBinder

unArgsBinder :: [Binder] -> [String]
unArgsBinder = map unArgBinder

unWhere :: ExpWhere -> Exp
unWhere (Where e ds) = Let ds e
unWhere (NoWhere e)  = e

-- Flatten a telescope, e.g., flatten (a b : A) (c : C) into
-- (a : A) (b : A) (c : C).
flattenTele :: Tele -> [VDecl]
flattenTele = concatMap (\(VDecl bs e) -> [VDecl [b] e | b <- bs])

-- Note: It is important to only apply unApps to e1 as otherwise the
-- structure of the application will be destroyed which leads to trouble
-- for constructor disambiguation!
unApps :: Exp -> [Exp]
unApps (App e1 e2) = unApps e1 ++ [e2]
unApps e           = [e]

unVar :: Exp -> Arg
unVar (Var b) = b
unVar e       = error $ "unVar bad input: " ++ show e

unVarBinder :: Exp -> String
unVarBinder = unArg . unVar

unPiDecl :: PiDecl -> VDecl
unPiDecl (PiDecl e t) = VDecl (map (Binder . unVar) (unApps e)) t

flattenTelePi :: [PiDecl] -> [VDecl]
flattenTelePi = flattenTele . map unPiDecl

namesTele :: Tele -> [String]
namesTele vs = unions [ unArgsBinder args | VDecl args _ <- vs ]

-------------------------------------------------------------------------------
-- | Resolver and environment

-- local environment for constructors
data Env = Env { constrs :: [String] }
         deriving (Eq, Show)

type Resolver a = ReaderT Env (StateT A.Prim (ErrorT String Identity)) a

emptyEnv :: Env
emptyEnv = Env []

runResolver :: Resolver a -> Either String a
runResolver x = runIdentity $ runErrorT $ evalStateT (runReaderT x emptyEnv) (0,"")

insertConstrs :: [String] -> Env -> Env
insertConstrs cs e@Env{constrs = cs'} = e{constrs = cs ++ cs'}

getEnv :: Resolver Env
getEnv = ask

getConstrs :: Resolver [String]
getConstrs = getEnv >>= return . constrs

genPrim :: Resolver A.Prim
genPrim = do
  prim <- lift get
  lift (modify (first succ))
  return prim

updateName :: String -> Resolver ()
updateName str = lift $ modify (\(g,_) -> (g,str))

lam :: Arg -> Resolver A.Exp -> Resolver A.Exp
lam a e = A.Lam (unArg a) <$> e

lams :: [Arg] -> Resolver A.Exp -> Resolver A.Exp
lams as e = foldr lam e as

resolveExp :: Exp -> Resolver A.Exp
resolveExp U            = return A.U
resolveExp Undef        = A.Undef <$> genPrim
resolveExp PN           = A.Undef <$> genPrim
resolveExp e@(App t s)  = do
  let x:xs = unApps e
  cs <- getConstrs
  if unVarBinder x `elem` cs
    then A.Con (unVarBinder x) <$> mapM resolveExp xs
    else A.App <$> resolveExp t <*> resolveExp s
resolveExp (Pi tele b)  = resolveTelePi (flattenTelePi tele) (resolveExp b)
resolveExp (Fun a b)    = A.Pi <$> resolveExp a <*> lam NoArg (resolveExp b)
resolveExp (Lam bs t)   = lams (map unBinder bs) (resolveExp t)
resolveExp (Split brs)  = A.Fun <$> genPrim <*> mapM resolveBranch brs
resolveExp (Let defs e) = A.lets <$> resolveDefs defs <*> resolveExp e
resolveExp (Var n)      = do
  let x = unArg n
  when (x == "_") (throwError "_ not a valid variable name")
  Env cs <- getEnv
  return (if x `elem` cs then A.Con x [] else A.Var x)

resolveWhere :: ExpWhere -> Resolver A.Exp
resolveWhere = resolveExp . unWhere

resolveBranch :: Branch -> Resolver (String,([String],A.Exp))
resolveBranch (Branch name args e) =
  ((unIdent name,) . (unArgs args,)) <$> resolveWhere e

-- Assumes a flattened telescope.
resolveTele :: [VDecl] -> Resolver [(String,A.Exp)]
resolveTele []                      = return []
resolveTele (VDecl [Binder a] t:ds) =
  ((unArg a,) <$> resolveExp t) <:> resolveTele ds
resolveTele ds                      =
  throwError $ "resolveTele: non flattened telescope " ++ show ds

-- Assumes a flattened telescope.
resolveTelePi :: [VDecl] -> Resolver A.Exp -> Resolver A.Exp
resolveTelePi [] b                      = b
resolveTelePi (VDecl [Binder x] a:as) b =
  A.Pi <$> resolveExp a <*> lam x (resolveTelePi as b)
resolveTelePi (t@(VDecl{}):as) _        =
  throwError ("resolveTelePi: non flattened telescope " ++ show t)

resolveLabel :: Sum -> Resolver (String,[(String,A.Exp)])
resolveLabel (Sum n tele) = (unIdent n,) <$> resolveTele (flattenTele tele)

resolveDefs :: [Def] -> Resolver [A.Def]
resolveDefs [] = return []
resolveDefs (DefTDecl n e:d:ds) = do
  e' <- resolveExp e
  xd <- checkDef (unIdent n) d
  rest <- resolveDefs ds
  return $ ([(unIdent n, e')],[xd]) : rest
resolveDefs (d:_) = error $ "Type declaration expected: " ++ show d

checkDef :: String -> Def -> Resolver (String,A.Exp)
checkDef n (Def (AIdent (_,m)) args body) | n == m = do
  updateName n
  (n,) <$> lams args (resolveWhere body)
checkDef n (DefData (AIdent (_,m)) args sums) | n == m = do
  updateName n
  (n,) <$> lams args (A.Sum <$> genPrim <*> mapM resolveLabel sums)
checkDef n d =
  throwError ("Mismatching names in " ++ show n ++ " and " ++ show d)