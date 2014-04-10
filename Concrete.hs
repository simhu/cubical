{-# LANGUAGE TupleSections, ParallelListComp #-}

-- | Convert the concrete syntax into the syntax of cubical TT.
module Concrete where

import Exp.Abs
import qualified CTT as C
import Pretty

import Control.Applicative
import Control.Monad.Trans
import Control.Monad.Trans.Reader
import Control.Monad.Trans.Error hiding (throwError)
import Control.Monad.Error (throwError)
import Control.Monad (when)
import Data.Functor.Identity
import Data.List (nub)

type Tele = [(AIdent,Exp)]
type Ter  = C.Ter

-- | Useful auxiliary functions

-- Applicative cons
(<:>) :: Applicative f => f a -> f [a] -> f [a]
a <:> b = (:) <$> a <*> b

-- un-something functions
unAIdent :: AIdent -> C.Ident
unAIdent (AIdent (_,x)) = x

unVar :: Exp -> Maybe AIdent
unVar (Var x) = Just x
unVar _       = Nothing

unWhere :: ExpWhere -> Exp
unWhere (Where e ds) = Let ds e
unWhere (NoWhere e)  = e

-- tail recursive form to transform a sequence of applications
-- App (App (App u v) ...) w  into (u, [v, …, w])
-- (cleaner than the previous version of unApps)
unApps :: Exp -> [Exp] -> (Exp, [Exp])
unApps (App u v) ws = unApps u (v : ws)
unApps u         ws = (u, ws)

vTele :: [VTDecl] -> Tele
vTele decls = [ (i, typ) | VTDecl id ids typ <- decls, i <- id:ids ]

-- turns an expression of the form App (... (App id1 id2) ... idn)
-- into a list of idents
pseudoIdents :: Exp -> Maybe [AIdent]
pseudoIdents = mapM unVar . uncurry (:) . flip unApps []

pseudoTele :: [PseudoTDecl] -> Maybe Tele
pseudoTele []                         = return []
pseudoTele (PseudoTDecl exp typ : pd) = do
    ids <- pseudoIdents exp
    pt  <- pseudoTele pd
    return $ map (,typ) ids ++ pt

-------------------------------------------------------------------------------
-- | Resolver and environment

data SymKind = Variable | Constructor
  deriving (Eq,Show)

-- local environment for constructors
data Env = Env { envModule :: String,
                 variables :: [(C.Binder,SymKind)] }
  deriving (Eq, Show)

type Resolver a = ReaderT Env (ErrorT String Identity) a

emptyEnv :: Env
emptyEnv = Env "" []

runResolver :: Resolver a -> Either String a
runResolver x = runIdentity $ runErrorT $ runReaderT x emptyEnv

updateModule :: String -> Env -> Env
updateModule mod e = e {envModule = mod}

insertBinder :: (C.Binder,SymKind) -> Env -> Env
insertBinder (x@(n,_),var) e
  | n == "_" || n == "undefined" = e
  | otherwise                    = e {variables = (x, var) : variables e}

insertBinders :: [(C.Binder,SymKind)] -> Env -> Env
insertBinders = flip $ foldr insertBinder

insertVar :: C.Binder -> Env -> Env
insertVar x = insertBinder (x,Variable)

insertVars :: [C.Binder] -> Env -> Env
insertVars = flip $ foldr insertVar

insertCon :: C.Binder -> Env -> Env
insertCon x = insertBinder (x,Constructor)

insertCons :: [C.Binder] -> Env -> Env
insertCons = flip $ foldr insertCon

getModule :: Resolver String
getModule = envModule <$> ask

getVariables :: Resolver [(C.Binder,SymKind)]
getVariables = variables <$> ask

getLoc :: (Int,Int) -> Resolver C.Loc
getLoc l = C.Loc <$> getModule <*> pure l

resolveBinder :: AIdent -> Resolver C.Binder
resolveBinder (AIdent (l,x)) = do l <- getLoc l; return (x, l)

resolveVar :: AIdent -> Resolver Ter
resolveVar (AIdent (l,x))
  | (x == "_") || (x == "undefined") = C.PN <$> C.Undef <$> getLoc l
  | otherwise = do
    modName <- getModule
    vars    <- getVariables
    case C.getIdent x vars of
      Just Variable    -> return $ C.Var x
      Just Constructor -> return $ C.Con x []
      _ -> throwError $
        "Cannot resolve variable" <+> x <+> "at position" <+>
        show l <+> "in module" <+> modName

lam :: AIdent -> Resolver Ter -> Resolver Ter
lam a e = do x <- resolveBinder a; C.Lam x <$> local (insertVar x) e

lams :: [AIdent] -> Resolver Ter -> Resolver Ter
lams = flip $ foldr lam

bind :: (Ter -> Ter -> Ter) -> (AIdent, Exp) -> Resolver Ter -> Resolver Ter
bind f (x,t) e = f <$> resolveExp t <*> lam x e

binds :: (Ter -> Ter -> Ter) -> Tele -> Resolver Ter -> Resolver Ter
binds f = flip $ foldr $ bind f

resolveExp :: Exp -> Resolver Ter
resolveExp U            = return C.U
resolveExp (Var x)      = resolveVar x
resolveExp (App t s)    = C.mkApps <$> resolveExp x <*> mapM resolveExp xs
  where (x, xs) = unApps t [s]
resolveExp (Sigma t b)  = case pseudoTele t of
  Just tele -> binds C.Sigma tele (resolveExp b)
  Nothing   -> throwError "telescope malformed in Sigma"
resolveExp (Pi t b)     =  case pseudoTele t of
  Just tele -> binds C.Pi tele (resolveExp b)
  Nothing   -> throwError "telescope malformed in Pigma"
resolveExp (Fun a b)    = bind C.Pi (AIdent ((0,0),"_"), a) (resolveExp b)
resolveExp (Lam x xs t) = lams (x:xs) (resolveExp t)
resolveExp (Fst t)      = C.Fst <$> resolveExp t
resolveExp (Snd t)      = C.Snd <$> resolveExp t
resolveExp (Pair t0 t1) = C.SPair <$> resolveExp t0 <*> resolveExp t1
resolveExp (Split brs)  = do
    brs' <- mapM resolveBranch brs
    loc  <- getLoc (case brs of Branch (AIdent (l,_)) _ _:_ -> l ; _ -> (0,0))
    return $ C.Split loc brs'
resolveExp (Let decls e) = do
  (rdecls,names) <- resolveDecls decls
  C.mkWheres rdecls <$> local (insertBinders names) (resolveExp e)

resolveWhere :: ExpWhere -> Resolver Ter
resolveWhere = resolveExp . unWhere

resolveBranch :: Branch -> Resolver (C.Label,([C.Binder],C.Ter))
resolveBranch (Branch lbl args e) = do
    binders <- mapM resolveBinder args
    re      <- local (insertVars binders) $ resolveWhere e
    return (unAIdent lbl, (binders, re))

resolveTele :: [(AIdent,Exp)] -> Resolver C.Tele
resolveTele []        = return []
resolveTele ((i,d):t) = do
  x <- resolveBinder i
  ((x,) <$> resolveExp d) <:> local (insertVar x) (resolveTele t)

resolveLabel :: Label -> Resolver (C.Binder, C.Tele)
resolveLabel (Label n vdecl) = (,) <$> resolveBinder n <*> resolveTele (vTele vdecl)

declsLabels :: [Decl] -> Resolver [C.Binder]
declsLabels decls = mapM resolveBinder [lbl | Label lbl _ <- sums]
  where sums = concat [sum | DeclData _ _ sum <- decls]

-- resolve Data or Def declaration
resolveDDecl :: Decl -> Resolver (C.Ident, C.Ter)
resolveDDecl (DeclDef  (AIdent (_,n)) args body) =
  (n,) <$> lams args (resolveWhere body)
resolveDDecl (DeclData x@(AIdent (l,n)) args sum) =
  (n,) <$> lams args (C.Sum <$> resolveBinder x <*> mapM resolveLabel sum)
resolveDDecl d = throwError $ "Definition expected " ++ show d

-- resolve mutual declarations (possibly one)
resolveMutuals :: [Decl] -> Resolver (C.Decls,[(C.Binder,SymKind)])
resolveMutuals decls = do
    binders <- mapM resolveBinder idents
    cs      <- declsLabels decls
    let cns = map fst cs ++ names
    when (nub cns /= cns) $
      throwError $ "Duplicated constructor or ident:" <+> show cns
    rddecls <-
      mapM (local (insertVars binders . insertCons cs) . resolveDDecl) ddecls
    when (names /= map fst rddecls) $
      throwError $ "Mismatching names in" <+> show decls
    rtdecls <- resolveTele tdecls
    return ([ (x,t,d) | (x,t) <- rtdecls | (_,d) <- rddecls ],
            map (,Constructor) cs ++ map (,Variable) binders)
  where
    idents = [ x | DeclType x _ <- decls ]
    names  = [ unAIdent x | x <- idents ]
    tdecls = [ (x,t) | DeclType x t <- decls ]
    ddecls = [ t | t <- decls, not $ isTDecl t ]
    isTDecl d = case d of DeclType {} -> True; _ -> False

resolveDecls :: [Decl] -> Resolver ([C.ODecls],[(C.Binder,SymKind)])
resolveDecls []                  = return ([],[])
resolveDecls (DeclOpaque n:ds) = do
  vars         <- getVariables
  (rest,names) <- resolveDecls ds
  case C.getBinder (unAIdent n) vars of
    Just x  -> return (C.Opaque x : rest, names)
    Nothing -> throwError $ "Not in scope " ++ show n
resolveDecls (DeclTransp n:ds) = do
  vars         <- getVariables
  (rest,names) <- resolveDecls ds
  case C.getBinder (unAIdent n) vars of
    Just x  -> return (C.Transparent x : rest, names)
    Nothing -> throwError $ "Not in scope" <+> show n
resolveDecls (td@(DeclType x t):ds) = case (C.mkPN (unAIdent x), ds) of
  (Just pn, ds) -> do
    b  <- resolveBinder x
    rt <- resolveExp t
    (rds,names) <- local (insertVar b) $ resolveDecls ds
    return (C.ODecls [(b, rt, C.PN pn)] : rds, names ++ [(b,Variable)])
  (Nothing, d:ds) -> do
    (rtd,names)  <- resolveMutuals [td,d]
    (rds,names') <- local (insertBinders names) $ resolveDecls ds
    return (C.ODecls rtd : rds, names' ++ names)
  (Nothing, []) -> throwError $
    "Missing definition for" <+> unAIdent x <+> "(not a primitive)"
resolveDecls (DeclMutual defs : ds) = do
  (rdefs,names)  <- resolveMutuals defs
  (rds,  names') <- local (insertBinders names) $ resolveDecls ds
  return (C.ODecls rdefs : rds, names' ++ names)
resolveDecls (decl:_) = throwError $ "Invalid declaration" <+> show decl

resolveModule :: Module -> Resolver ([C.ODecls],[(C.Binder,SymKind)])
resolveModule (Module id imports decls) =
  local (updateModule $ unAIdent id) $ resolveDecls decls

resolveModules :: [Module] -> Resolver ([C.ODecls],[(C.Binder,SymKind)])
resolveModules []         = return ([],[])
resolveModules (mod:mods) = do
  (rmod, names)  <- resolveModule mod
  (rmods,names') <- local (insertBinders names) $ resolveModules mods
  return (rmod ++ rmods, names' ++ names)
