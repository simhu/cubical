{-# LANGUAGE TupleSections #-}

-- Convert the concrete syntax into the syntax of miniTT.
module Concrete where

import Exp.Abs
-- import qualified MTT as M
import qualified CTT as C

import Control.Arrow (first)
import Control.Applicative
import Control.Monad.Trans
import Control.Monad.Trans.State
import Control.Monad.Trans.Reader
import Control.Monad.Trans.Error hiding (throwError)
import Control.Monad.Error (throwError)
import Control.Monad (when)
import Data.Functor.Identity
import Data.List (union)

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
data Env = Env { fileEnv      :: String,
                 constructors :: [String],
                 variables    :: (String, (Int,Int))}
         deriving (Eq, Show)

type Resolver a = ReaderT Env (ErrorT String Identity) a

emptyEnv :: Env
emptyEnv = Env "" [] []

runResolver :: Resolver a -> Either String a
runResolver x = runIdentity $ runErrorT $ runReaderT x emptyEnv

updateFile :: String -> Env -> Env
updateFile file e = e {fileEnv = file}

insertConstructors :: [String] -> Env -> Env
insertConstructors cs (Env cs') = Env $ cs ++ cs'

getEnv :: Resolver Env
getEnv = ask

getConstructors :: Resolver [String]
getConstructors = constructors <$> getEnv

lam :: Arg -> Resolver C.Ter -> Resolver C.Ter
lam a e = C.Lam (unArg a) <$> e

lams :: [Arg] -> Resolver C.Ter -> Resolver C.Ter
lams as e = foldr lam e as

resolveExp :: Exp -> Resolver C.Ter
resolveExp U            = return C.U
resolveExp Undef        = C.PN <$> genPN
resolveExp PN           = C.PN <$> genPN
resolveExp e@(App t s)  = do
  let x:xs = unApps e
  cs <- getConstructors
  case x of
    Var a -> let n = unArg a in
      if n `elem` cs then C.Con n <$> mapM resolveExp xs
      else C.App <$> resolveExp t <*> resolveExp s
    _ -> C.App <$> resolveExp t <*> resolveExp s
resolveExp (Pi tele b)  = resolveTelePi (flattenTelePi tele) (resolveExp b)
resolveExp (Sigma tele b)  = resolveTeleSigma (flattenTelePi tele) (resolveExp b)
resolveExp (Fun a b)    = C.Pi <$> resolveExp a <*> lam NoArg (resolveExp b)
resolveExp (Lam bs t)   = lams (map unBinder bs) (resolveExp t)
resolveExp (Fst t)      = C.Fst <$> resolveExp t
resolveExp (Snd t)      = C.Snd <$> resolveExp t
resolveExp (Pair t0 t1) = C.SPair <$> resolveExp t0 <*> resolveExp t1
resolveExp (Split brs)  = C.Split <$> genPrim <*> mapM resolveBranch brs
resolveExp (Let defs e) = C.mkWheres <$> resolveDefs defs <*> resolveExp e
resolveExp (Var n)      = do
  let x = unArg n
  when (x == "_") (throwError "_ not a valid variable name")
  Env cs <- getEnv
  return (if x `elem` cs then C.Con x [] else C.Var x)

resolveWhere :: ExpWhere -> Resolver C.Ter
resolveWhere = resolveExp . unWhere

resolveBranch :: Branch -> Resolver (String,([String],C.Ter))
resolveBranch (Branch name args e) =
  ((unIdent name,) . (unArgs args,)) <$> resolveWhere e

-- Assumes a flattened telescope.
resolveTele :: [VDecl] -> Resolver [(String,C.Ter)]
resolveTele []                      = return []
resolveTele (VDecl [Binder a] t:ds) =
  ((unArg a,) <$> resolveExp t) <:> resolveTele ds
resolveTele ds                      =
  throwError $ "resolveTele: non flattened telescope " ++ show ds

-- Assumes a flattened telescope.
resolveTelePi :: [VDecl] -> Resolver C.Ter -> Resolver C.Ter
resolveTelePi [] b                      = b
resolveTelePi (VDecl [Binder x] a:as) b =
  C.Pi <$> resolveExp a <*> lam x (resolveTelePi as b)
resolveTelePi (t@(VDecl{}):as) _        =
  throwError ("resolveTelePi: non flattened telescope " ++ show t)

-- Assumes a flattened telescope.
resolveTeleSigma :: [VDecl] -> Resolver C.Ter -> Resolver C.Ter
resolveTeleSigma [] b                      = b
resolveTeleSigma (VDecl [Binder x] a:as) b =
  C.Sigma <$> resolveExp a <*> lam x (resolveTeleSigma as b)
resolveTeleSigma (t@(VDecl{}):as) _        =
  throwError ("resolveTeleSigma: non flattened telescope " ++ show t)

resolveLabel :: Sum -> Resolver (String,[(String,C.Ter)])
resolveLabel (Sum n tele) = (unIdent n,) <$> resolveTele (flattenTele tele)

resolveDefs :: [Def] -> Resolver [C.Def]
resolveDefs []                  = return []
resolveDefs (DefTDecl n e:d:ds) = do
  e' <- resolveExp e
  xd <- checkDef (unIdent n,d)
  rest <- resolveDefs ds
  return $ ([(unIdent n, e')],[xd]) : rest
resolveDefs (DefMutual defs:ds) = resolveMutual defs <:> resolveDefs ds
resolveDefs (d:_) = error $ "Type declaration expected: " ++ show d

checkDef :: (String,Def) -> Resolver (String,C.Ter)
checkDef (n,Def (AIdent (_,m)) args body) | n == m = do
  updateName n
  (n,) <$> lams args (resolveWhere body)
checkDef (n,DefData (AIdent (_,m)) args sums) | n == m = do
  updateName n
  (n,) <$> lams args (C.Sum <$> genPrim <*> mapM resolveLabel sums)
checkDef (n,d) =
  throwError ("Mismatching names in " ++ show n ++ " and " ++ show d)

resolveMutual :: [Def] -> Resolver C.Def
resolveMutual defs = do
  tdecls' <- mapM resolveTDecl tdecls
  let names = map fst tdecls'
  when (length names /= length decls) $
    throwError $ "Definitions missing in " ++ show defs
  tdef' <- mapM checkDef (zip names decls)
  return (tdecls',tdef')
  where
    (tdecls,decls) = span isTDecl defs
    isTDecl d@(DefTDecl {}) = True
    isTDecl _               = False
    resolveTDecl (DefTDecl n e) = do e' <- resolveExp e
                                     return (unIdent n, e')
