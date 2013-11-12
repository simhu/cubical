-- Convert the concrete syntax into the syntax of miniTT.

-- TODO: rename into Concrete.hs or ..?
module Concr where

import qualified Exp.Abs as A
import MTT3
import Control.Monad.Trans.Reader
import Control.Monad.Trans.Error hiding (throwError)
import Control.Monad.Error (throwError)
import Data.Functor.Identity
import Data.List (elemIndex)
import Control.Applicative

type LEnv = [String]            -- local environment for variables

type Resolver = ReaderT LEnv (ErrorT String Identity)

runResolver :: Resolver a -> a
runResolver x = case runIdentity $ runErrorT $ runReaderT x [] of
  Left e -> error e
  Right a -> a

look :: A.AIdent -> Resolver Exp
look iden@(A.AIdent (_, str)) = do
  e <- ask
  case elemIndex str e of
    Just n  -> return $ Ref n
    Nothing -> throwError ("unknown identifier: " ++ show iden)

-- Insert a variable in an environment.
insertVar :: A.Arg -> LEnv -> LEnv
insertVar (A.Arg (A.AIdent (_,str))) e = str:e
insertVar A.NoArg                    e = "_":e

-- Note: reverses order
insertVars :: [A.Arg] -> LEnv -> LEnv
insertVars as e = foldl (flip insertVar) e as
-- insertVars [] e = e
-- insertVars (a:as) e = insertVars as (insertVar a e)

-- A dummy variable we can insert when we have to lift an
-- environment.
dummyVar :: A.Arg
dummyVar = A.NoArg

resolveVar :: A.Arg -> Resolver Exp
resolveVar (A.Arg i) = look i
resolveVar A.NoArg   = throwError "_ not a valid variable name "

unNE :: A.VDeclNE -> A.VDecl
unNE (A.VDeclNE vdcl) = vdcl

unBinder :: A.Binder -> A.Arg
unBinder (A.Binder b) = b

-- Flatten a telescope, e.g., flatten (a b : A) (c : C) into
-- (a : A) (b : A) (c : C).
flattenTele :: [A.VDecl] -> [A.VDecl]
flattenTele = concatMap $ \(A.VDecl bs e) -> [A.VDecl [b] e | b <- bs]

-- Assumes the telescope is flattened.
resolveTelePi :: [A.VDecl] -> Resolver Exp -> Resolver Exp
resolveTelePi [] b = b
resolveTelePi ((A.VDecl [A.Binder x] a):as) b =
  Pi <$> resolveExp a <*> lam x (resolveTelePi as b)
resolveTelePi (t@(A.VDecl _ _):as) _ =
  throwError ("resolveTelePi: non flattened telescope " ++ show t)

lam :: A.Arg -> Resolver Exp -> Resolver Exp
lam a e = Lam <$> local (insertVar a) e

resolveLams :: [A.Arg] -> Resolver Exp -> Resolver Exp
resolveLams as e = foldr lam e as

resolveExp :: A.Exp -> Resolver Exp
resolveExp A.U = return U
resolveExp (A.Var (A.Binder a)) = resolveVar a
resolveExp (A.App t s) = App <$> resolveExp t <*> resolveExp s
resolveExp (A.Pi (A.TeleNE tele) b) =
  resolveTelePi (flattenTele (map unNE tele)) (resolveExp b)
resolveExp (A.Fun a b) =
  Pi <$> resolveExp a <*> lam dummyVar (resolveExp b)
resolveExp (A.Lam bs t) = resolveLams (map unBinder bs) (resolveExp t)
resolveExp (A.Case e brs) =
  App <$> (Fun <$> mapM resolveBranch brs) <*> resolveExp e
resolveExp (A.Let defs e) = do
  exp     <- resolveExp e       -- FIXME: e should know about the definitions!
  exptyps <- resolveMutualDefs defs
  let (exps,typs) = unzip exptyps
  return (Def exp exps typs)

resolveExpWhere :: A.ExpWhere -> Resolver Exp
resolveExpWhere (A.Where e defs) = resolveExp (A.Let defs e)
resolveExpWhere (A.NoWhere e)    = resolveExp e

resolveBranch :: A.Branch -> Resolver (String,Exp)
resolveBranch (A.Branch (A.AIdent (_,name)) args e) = do
  exp <- local (insertVars args) (resolveExpWhere e)
  return (name,exp)

-- Assumes a flattened telescope.
resolveTele :: [A.VDecl] -> Resolver [Exp]
resolveTele [] = return []
resolveTele (A.VDecl [A.Binder a] t:ds) =
  (:) <$> resolveExp t <*> local (insertVar a) (resolveTele ds)
resolveTele ds =
  throwError ("resolveTele: non flattened telescope " ++ show ds)

resolveLabel :: A.Sum -> Resolver (String,[Exp])
resolveLabel (A.Sum (A.AIdent (_,name)) (A.Tele tele)) =
  resolveTele (flattenTele tele) >>= \ts -> return (name, ts)

unData :: A.Def -> Resolver (A.AIdent,Exp,Exp)
unData (A.DefData iden (A.Tele vdcls) cs) = do
  let flat   = flattenTele vdcls
  let args   = concatMap (\(A.VDecl binds _) -> map unBinder binds) flat
  let labels = Sum <$> mapM (local (insertVars args) . resolveLabel) cs
  exp <- resolveLams args labels
  typ <- resolveTelePi flat (return U) -- data-decls. have value type U
  return (iden,exp,typ)
unData def = throwError ("unData: data declaration expected " ++ show def)

-- All the defs are mutual.
-- TODO: optimize with call-graph.  Then the result type should be
-- Resolver Env instead (or Resolver [Env] ?).
resolveMutualDefs :: [A.Def] -> Resolver [(Exp,Exp)]
resolveMutualDefs [] = return []
resolveMutualDefs (def:defs) = case def of -- TODO: code-duplication (last 2 cases)
  A.DefData{} -> do
    (iden,exp,typ) <- unData def
    rest <- local (insertVar (A.Arg iden)) (resolveMutualDefs defs)
    return ((exp,typ):rest)
  A.DefTDecl iden t -> do
    (A.Def _ args body,defs') <- findDef iden defs
    exp <- resolveLams args (local (insertVars args) (resolveExpWhere body))
    typ <- resolveExp t
    rest <- local (insertVar (A.Arg iden)) (resolveMutualDefs defs')
    return ((exp,typ):rest)
  A.Def iden args body -> do
    (A.DefTDecl _ t, defs') <- findTDecl iden defs
    exp <- resolveLams args (local (insertVars args) (resolveExpWhere body))
    typ <- resolveExp t
    rest <- local (insertVar (A.Arg iden)) (resolveMutualDefs defs')
    return ((exp,typ):rest)
  where
    -- pick out a definition
    findDef :: A.AIdent -> [A.Def] -> Resolver (A.Def, [A.Def])
    findDef iden []         =
      throwError (show iden ++ " is lacking an accompanying binding")
    findDef iden@(A.AIdent (_,name)) (def:defs) = case def of
      A.Def (A.AIdent (_,name')) _ _ | name == name' -> return (def,defs)
      _                                              ->
        findDef iden defs >>= \(d,ds) -> return (d, def:ds)

    -- pick out a type declaration
    findTDecl :: A.AIdent -> [A.Def] -> Resolver (A.Def, [A.Def])
    findTDecl iden []         =
      throwError (show iden ++ " is lacking an accompanying type declaration")
    findTDecl iden@(A.AIdent (_,name)) (def:defs) = case def of
      A.DefTDecl (A.AIdent (_,name')) _ | name == name' -> return (def,defs)
      _                                                 ->
        findTDecl iden defs >>= \(d,ds) -> return (d, def:ds)

