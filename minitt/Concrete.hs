-- Convert the concrete syntax into the syntax of miniTT.
module Concrete where

import Exp.Abs
import qualified MTT as A

import Control.Monad.Trans.Reader
import Control.Monad.Trans.Error hiding (throwError)
import Control.Monad.Error (throwError)
import Data.Functor.Identity
import Data.List (elemIndex)
import Control.Applicative

type LEnv = [String]            -- local environment for variables

type Resolver = ReaderT LEnv (ErrorT String Identity)

runResolver :: Resolver a -> Either String a
runResolver x = runIdentity $ runErrorT $ runReaderT x []

resolveModule :: Module -> Resolver [(A.Exp,A.Exp)]
resolveModule (Module defs) = resolveMutualDefs defs

look :: AIdent -> Resolver A.Exp
look iden@(AIdent (_, str)) = do
  e <- ask
  case elemIndex str e of
    Just n  -> return $ A.Ref n
    Nothing -> throwError ("unknown identifier: " ++ show iden)

-- Insert a variable in an environment.
insertVar :: Arg -> LEnv -> LEnv
insertVar (Arg (AIdent (_,str))) e = str:e
insertVar NoArg                  e = "_":e

-- Note: reverses order
insertVars :: [Arg] -> LEnv -> LEnv
insertVars as e = foldl (flip insertVar) e as

-- A dummy variable we can insert when we have to lift an
-- environment.
dummyVar :: Arg
dummyVar = NoArg

resolveVar :: Arg -> Resolver A.Exp
resolveVar (Arg i) = look i
resolveVar NoArg   = throwError "_ not a valid variable name "

unNE :: VDeclNE -> VDecl
unNE (VDeclNE vdcl) = vdcl

unBinder :: Binder -> Arg
unBinder (Binder b) = b

-- Flatten a telescope, e.g., flatten (a b : A) (c : C) into
-- (a : A) (b : A) (c : C).
flattenTele :: [VDecl] -> [VDecl]
flattenTele = concatMap $ \(VDecl bs e) -> [VDecl [b] e | b <- bs]

-- Assumes the telescope is flattened.
resolveTelePi :: [VDecl] -> Resolver A.Exp -> Resolver A.Exp
resolveTelePi [] b = b
resolveTelePi ((VDecl [Binder x] a):as) b =
  A.Pi <$> resolveExp a <*> lam x (resolveTelePi as b)
resolveTelePi (t@(VDecl{}):as) _ =
  throwError ("resolveTelePi: non flattened telescope " ++ show t)

lam :: Arg -> Resolver A.Exp -> Resolver A.Exp
lam a e = A.Lam <$> local (insertVar a) e

resolveLams :: [Arg] -> Resolver A.Exp -> Resolver A.Exp
resolveLams as e = foldr lam e as

resolveExp :: Exp -> Resolver A.Exp
resolveExp U                    = return A.U
resolveExp (Var (Binder a))     = resolveVar a
resolveExp (App t s)            = A.App <$> resolveExp t <*> resolveExp s
resolveExp (Pi (TeleNE tele) b) =
  resolveTelePi (flattenTele (map unNE tele)) (resolveExp b)
resolveExp (Fun a b) =
  A.Pi <$> resolveExp a <*> lam dummyVar (resolveExp b)
resolveExp (Lam bs t)   = resolveLams (map unBinder bs) (resolveExp t)
resolveExp (Case e brs) =
  A.App <$> (A.Fun <$> mapM resolveBranch brs) <*> resolveExp e
resolveExp (Let defs e) = do
  exp     <- resolveExp e       -- FIXME: e should know about the definitions!
  exptyps <- resolveMutualDefs defs
  let (exps,typs) = unzip exptyps
  return (A.Def exp exps typs)

resolveExpWhere :: ExpWhere -> Resolver A.Exp
resolveExpWhere (Where e defs) = resolveExp (Let defs e)
resolveExpWhere (NoWhere e)    = resolveExp e

resolveBranch :: Branch -> Resolver (String,A.Exp)
resolveBranch (Branch (AIdent (_,name)) args e) = do
  exp <- local (insertVars args) (resolveExpWhere e)
  return (name,exp)

-- Assumes a flattened telescope.
resolveTele :: [VDecl] -> Resolver [A.Exp]
resolveTele []                      = return []
resolveTele (VDecl [Binder a] t:ds) =
  (:) <$> resolveExp t <*> local (insertVar a) (resolveTele ds)
resolveTele ds =
  throwError ("resolveTele: non flattened telescope " ++ show ds)

resolveLabel :: Sum -> Resolver (String,[A.Exp])
resolveLabel (Sum (AIdent (_,name)) (Tele tele)) =
  resolveTele (flattenTele tele) >>= \ts -> return (name, ts)

-- Anders: Also output a list of constructor names
unData :: Def -> Resolver (AIdent,[Arg],A.Exp,A.Exp)
unData (DefData iden (Tele vdcls) cs) = do
  let flat = flattenTele vdcls
  let args = concatMap (\(VDecl binds _) -> map unBinder binds) flat
  let cons = [ Arg id | Sum id _ <- cs ]
  let labels = A.Sum <$> mapM (local (insertVars args) . resolveLabel) cs
  -- Anders: I think we should add the name of the data type when resolving
  --         the sums.      
  exp <- resolveLams (Arg iden : args) labels
  typ <- resolveTelePi flat (return A.U) -- data-decls. have value type U
  return (iden,cons,exp,typ)
unData def = throwError ("unData: data declaration expected " ++ show def)

-- All the defs are mutual.
-- TODO: optimize with call-graph. Then the result type should be
-- Resolver Env instead (or Resolver [Env] ?).
resolveMutualDefs :: [Def] -> Resolver [(A.Exp,A.Exp)]
resolveMutualDefs []         = return []
resolveMutualDefs (def:defs) = case def of -- TODO: code-duplication (last 2 cases)
  DefData{} -> do
    (iden,args,exp,typ) <- unData def
    -- Anders: Now that the constructor names are known we can add them
    rest <- local (insertVars (Arg iden : args)) (resolveMutualDefs defs)
    return ((exp,typ):rest)
  DefTDecl iden t -> do
    (Def _ args body,defs') <- findDef iden defs
    exp <- resolveLams args (local (insertVars args) (resolveExpWhere body))
    typ <- resolveExp t
    rest <- local (insertVar (Arg iden)) (resolveMutualDefs defs')
    return ((exp,typ):rest)
  Def iden args body -> do
    (DefTDecl _ t, defs') <- findTDecl iden defs
    -- TODO: There is a bug here for recursive definitions!
    --exp <- resolveLams args (resolveExpWhere body)
    exp <- resolveLams args (local (insertVars args) (resolveExpWhere body))
    typ <- resolveExp t
    rest <- local (insertVar (Arg iden)) (resolveMutualDefs defs')
    return ((exp,typ):rest)
  where
    -- pick out a definition
    findDef :: AIdent -> [Def] -> Resolver (Def,[Def])
    findDef iden []         =
      throwError (show iden ++ " is lacking an accompanying binding")
    findDef iden@(AIdent (_,name)) (def:defs) = case def of
      Def (AIdent (_,name')) _ _ | name == name' -> return (def,defs)
      _                                              ->
        findDef iden defs >>= \(d,ds) -> return (d, def:ds)

    -- pick out a type declaration
    findTDecl :: AIdent -> [Def] -> Resolver (Def,[Def])
    findTDecl iden []         =
      throwError (show iden ++ " is lacking an accompanying type declaration")
    findTDecl iden@(AIdent (_,name)) (def:defs) = case def of
      DefTDecl (AIdent (_,name')) _ | name == name' -> return (def,defs)
      _                                                 ->
        findTDecl iden defs >>= \(d,ds) -> return (d, def:ds)


--------------------------------------------------------------------------------
-- TESTS:      

-- test for unData: nat
nat = DefData (AIdent ((8,6),"N")) (Tele []) 
       [Sum (AIdent ((8,10),"zero")) (Tele []),
        Sum (AIdent ((8,17),"suc")) 
          (Tele [VDecl [Binder (Arg (AIdent ((8,22),"n")))] 
                   (Var (Binder (Arg (AIdent ((8,26),"N")))))])]

-- runResolver $ resolveMutualDefs [nat,idNt,idNdef]
idNt = DefTDecl (AIdent ((35,1),"id")) (Fun (Var (Binder (Arg (AIdent ((35,6),"N"))))) (Var (Binder (Arg (AIdent ((35,11),"N"))))))
idNdef = Def (AIdent ((36,1),"id")) [Arg (AIdent ((36,4),"x"))] (NoWhere (Var (Binder (Arg (AIdent ((36,8),"x"))))))

-- runResolver $ resolveMutualDefs [idUt,idUdef]
idUt = DefTDecl (AIdent ((35,1),"id")) (Fun U U)
idUdef = Def (AIdent ((36,1),"id")) [Arg (AIdent ((36,4),"x"))] (NoWhere (Var (Binder (Arg (AIdent ((36,8),"x"))))))
