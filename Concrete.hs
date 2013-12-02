-- Convert the concrete syntax into the syntax of miniTT.
module Concrete where

import Exp.Abs
import qualified MTT as A

import Control.Applicative
import Control.Monad.Trans.Reader
import Control.Monad.Trans.Error hiding (throwError)
import Control.Monad.Error (throwError)
import Data.Functor.Identity
import Data.Function
import Data.Graph
import Data.List
import Data.Maybe

-- | Useful auxiliary functions
unions :: Eq a => [[a]] -> [a]
unions = foldr union []

-- A cute combinator
(<:>) :: Applicative f => f a -> f [a] -> f [a]
a <:> b = (:) <$> a <*> b

-- local environment for variables
type LEnv = [String]

type Resolver = ReaderT LEnv (ErrorT String Identity)

runResolver :: Resolver a -> Either String a
runResolver x = runIdentity $ runErrorT $ runReaderT x []

look :: AIdent -> Resolver A.Exp
look iden@(AIdent (_, str)) = do
  e <- ask
  case elemIndex str e of       -- TODO: exclude "_"
    Just n  -> return $ A.Ref n
    Nothing -> throwError ("unknown identifier: " ++ show iden)

-- Insert a variable in an environment.
insertVar :: Arg -> LEnv -> LEnv
insertVar (Arg (AIdent (_,str))) e = str:e
insertVar NoArg                  e = "_":e

-- Note: reverses order
insertVars :: [Arg] -> LEnv -> LEnv
insertVars as e = foldl (flip insertVar) e as

insertNames :: [String] -> LEnv -> LEnv
insertNames = (++) . reverse 

resolveVar :: Arg -> Resolver A.Exp
resolveVar (Arg i) = look i
resolveVar NoArg   = throwError "_ not a valid variable name "

-- un-something functions
unArg :: Arg -> String
unArg a = head $ insertVar a []

unArgs :: [Arg] -> [String]
unArgs = map unArg

unNE :: VDeclNE -> VDecl
unNE (VDeclNE vdcl) = vdcl

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
flattenTele :: [VDecl] -> [VDecl]
flattenTele = concatMap $ \(VDecl bs e) -> [VDecl [b] e | b <- bs]

flattenTeleNE :: [VDeclNE] -> [VDecl]
flattenTeleNE = flattenTele . map unNE

-- Assumes the telescope is flattened.
resolveTelePi :: [VDecl] -> Resolver A.Exp -> Resolver A.Exp
resolveTelePi [] b = b
resolveTelePi ((VDecl [Binder x] a):as) b =
  A.Pi <$> resolveExp a <*> lam x (resolveTelePi as b)
resolveTelePi (t@(VDecl{}):as) _ =
  throwError ("resolveTelePi: non flattened telescope " ++ show t)

lam :: Arg -> Resolver A.Exp -> Resolver A.Exp
lam a e= A.Lam <$> local (insertVar a) e

lams :: [Arg] -> Resolver A.Exp -> Resolver A.Exp
lams as e = foldr lam e as

resolveExp :: Exp -> Resolver A.Exp
resolveExp U                       = return A.U
resolveExp (Var (Binder a))        = resolveVar a
resolveExp (App t s)               = A.App <$> resolveExp t <*> resolveExp s
resolveExp (Pi (TeleNE tele) b)    =
  resolveTelePi (flattenTeleNE tele) (resolveExp b)
resolveExp (Fun a b)               =
  A.Pi <$> resolveExp a <*> lam NoArg (resolveExp b)
resolveExp (Lam bs t)              = lams (map unBinder bs) (resolveExp t)
-- resolveExp (Case e brs) =
--   A.App <$> (A.Fun <$> mapM resolveBranch brs) <*> resolveExp e
resolveExp (Split brs)             = A.Fun <$> mapM resolveBranch brs
resolveExp (Let defs e)            = handleDefs defs (resolveExp e)
resolveExp (Con (AIdent (_,c)) es) = A.Con c <$> mapM resolveExp es
resolveExp (PN (AIdent (_,n)) t)   = A.PN n <$> resolveExp t
resolveExp Top                     = return A.Top

resolveExpWhere :: ExpWhere -> Resolver A.Exp
resolveExpWhere = resolveExp . unWhere

resolveBranch :: Branch -> Resolver (String,A.Exp)
resolveBranch (Branch (AIdent (_,name)) args e) = do
  exp <- local (insertVars args) (resolveExpWhere e)
  return (name,exp)

-- Assumes a flattened telescope.
resolveTele :: [VDecl] -> Resolver [A.Exp]
resolveTele []                      = return []
resolveTele (VDecl [Binder a] t:ds) =
  resolveExp t <:> local (insertVar a) (resolveTele ds)
resolveTele ds =
  throwError ("resolveTele: non flattened telescope " ++ show ds)

resolveLabel :: Sum -> Resolver (String,[A.Exp])
resolveLabel (Sum (AIdent (_,name)) (Tele tele)) =
  ((,) name) <$> resolveTele (flattenTele tele)

--------------------------------------------------------------------------------
-- Call graph

callGraph :: [Def] -> [[[Def]]]
callGraph = filter (/= [[]]) . map flattenSCC . stronglyConnComp . graph

graph :: [Def] -> [([Def],String,[String])]
graph = map ((\(as,b:_,xs) -> (concat as,b,concat xs)) . unzip3)
      . groupBy ((==) `on` (\(_,n,_) -> n)) . concatMap defToGraph

defToGraph :: Def -> [([Def], String, [String])]
defToGraph d = case d of
  (Def (AIdent (_,iden)) args body) ->
    [([d],iden,freeVars (unWhere body) \\ unArgs args)]
  (DefTDecl (AIdent (_,iden)) exp) -> [([d],iden,freeVars exp)]
  (DefData (AIdent (_,iden)) (Tele vdecls) labels) ->
       ([d],iden,freeVarsTele vdecls `union` fvB)
     : [ ([],c,[iden]) | Sum (AIdent (_,c)) _ <- labels ]
    where fvB = unions [ freeVarsTele tele \\ namesTele tele
                       | Sum _ (Tele tele) <- labels ]
  (DefPrim defs) -> graph (concatMap unfoldPrimitive defs)

-- etaExpand :: Resolver A.Exp -> Exp -> Resolver A.Exp
-- etaExpand t (Pi (TeleNe vs) b) = etaExpand (lams args (apps t vars)) b
--   where args = map (unBinder . unNE) vs
--         vars = mapM resolveVar args
-- etaExpand t _       = t

-- teleToArgs :: [VDecl] -> [Arg]
-- teleToArgs (VDecl bs _:vs) = map unBinder bs ++ teleToArgs vs

-- -- Assumes the free variables of t don't clash with the variables of
-- -- the Pi-variables in the type.
-- etaExpand :: Exp -> Exp -> Exp
-- etaExpand t (Pi (TeleNe vs) b) = etaExpand (Lams args (apps t vars))
--   where args = teleToArgs (map unNe vs)
--         vars = map

unfoldPrimitive :: Def -> [Def]
unfoldPrimitive d@(DefTDecl n a) = [d,decl]
  where decl = Def n [] (NoWhere (PN n a)) -- add a declaration using PN
unfoldPrimitive d =             -- TODO: better error handling?
  error ("only type declarations are allowed in primitives " ++ show d)

freeVars :: Exp -> [String]
freeVars (Let ds e)  = (freeVars e `union` unions (map freeVarsDef ds))
                       \\ defsToNames ds
freeVars (Lam bs e)  = freeVars e \\ unArgsBinder bs
freeVars (Split bs) =
  unions [ str:(freeVars (unWhere e) \\ unArgs args)
         | Branch (AIdent (_,str)) args e <- bs ]
-- freeVars (Case e bs) =
--   freeVars e `union` unions [ str:(freeVars (unWhere ew) \\ unArgs args)
--                             | Branch (AIdent (_,str)) args ew <- bs ]
freeVars (Fun e1 e2) = freeVars e1 `union` freeVars e2
freeVars (Pi (TeleNE []) e) = freeVars e
freeVars (Pi (TeleNE (VDeclNE (VDecl bs a):vs)) e) =
  freeVars a `union` (freeVars (Pi (TeleNE vs) e) \\ unArgsBinder bs)
freeVars (App e1 e2) = freeVars e1 `union` freeVars e2
freeVars (Var x)     = [unArgBinder x]
freeVars U           = []
freeVars (Con (AIdent (_,str)) es)  = [str] `union` unions (map freeVars es)
freeVars (PN _ t)    = freeVars t
-- freeVars (PN (AIdent (_,n)) ns t) =
--   freeVars t `union` map (\(AIdent (_,i)) -> i) ns
-- freeVars (PN (AIdent (_,n)) t) = --[n] `union` freeVars t -- ?
--   freeVars t
--freeVars (PN _ t es) = unions (map freeVars es)

-- The free variables of the right hand side.
freeVarsDef :: Def -> [String]
freeVarsDef (Def _ args exp) = freeVars (unWhere exp) \\ unArgs args
freeVarsDef (DefTDecl _ exp) = freeVars exp
freeVarsDef (DefData _ (Tele vdecls) labels) = freeVarsTele vdecls `union`
  (unions [ freeVarsTele vs | Sum _ (Tele vs) <- labels ] \\ namesTele vdecls)
freeVarsDef (DefPrim defs) = unions (map freeVarsDef defs)

freeVarsTele :: [VDecl] -> [String]
freeVarsTele []                = []
freeVarsTele ((VDecl bs e):ds) =
  freeVars e `union` (freeVarsTele ds \\ unArgsBinder bs)

namesTele :: [VDecl] -> [String]
namesTele vs = unions [ unArgsBinder args | VDecl args _ <- vs ]

defToNames :: Def -> [String]
defToNames (Def (AIdent (_,n)) _ _)     = [n]
defToNames (DefTDecl (AIdent (_,n)) _)  = [n]
defToNames (DefData (AIdent (_,n)) _ _) = [n]
defToNames (DefPrim defs)               = defsToNames defs

defsToNames :: [Def] -> [String]
defsToNames = nub . concatMap defToNames

--------------------------------------------------------------------------------
--

unData' :: Def -> [String] -> Resolver (A.Exp,A.Exp)
unData' (DefData _ (Tele vdcls) cs) ns = do
  let flat = flattenTele vdcls
  let args = concatMap (\(VDecl binds _) -> map unBinder binds) flat
  let labels = A.Sum <$> mapM resolveLabel cs
-- A.Sum <$> mapM (local (insertVars args . insertNames ns) . resolveLabel) cs
  exp <- local (insertNames ns) $ lams args labels
  typ <- resolveTelePi flat (return A.U) -- data-decls. have type U
  return (exp,typ)
unData' def _ = throwError ("unData: data declaration expected " ++ show def)

handleMutual :: [[Def]] -> [String] -> Resolver [([String],A.Exp,A.Exp)]
handleMutual []       _  = return []
handleMutual (ds:dss) ns = case sort ds of -- use Ord for Def: will put Def before DefTDecl
  [d@DefData{}]        -> do
    (exp,typ) <- unData' d ns
    rest <- handleMutual dss ns
    return ((ns,exp,typ):rest)
  [Def iden args body,DefTDecl _ t] -> do
    exp <- local (insertNames ns) $ lams args (resolveExpWhere body)
    typ <- resolveExp t
    rest <- handleMutual dss ns
    return ((ns,exp,typ):rest)
  x -> throwError $ "handleMutual: Something is missing or too many "
                  ++ "definition/declarations: " ++ show x

--                                        names, exp : type
handleMutuals :: [[[Def]]] -> Resolver [[([String],A.Exp,A.Exp)]]
handleMutuals [] = return []
handleMutuals (ds:dss) = do
  let ns = defsToNames $ concat ds
  xs <- handleMutual ds ns
  (xs :) <$> local (insertNames ns) (handleMutuals dss)

handleLet :: A.Exp -> [[([String],A.Exp,A.Exp)]] -> A.Exp
handleLet e []     = e
handleLet e (x:xs) = A.Def (handleLet e xs) es ts ns
  where (nss,es,ts) = unzip3 x
        ns          = concat nss

handleDefs :: [Def] -> Resolver A.Exp -> Resolver A.Exp
handleDefs defs re = do
  let cg = callGraph defs
  let ns = defsToNames $ concat $ concat cg
  xs <- handleMutuals cg
  e  <- local (insertNames ns) re
  return (handleLet e xs)

handleModule :: Module -> Resolver A.Exp
handleModule (Module defs) = handleDefs defs (return A.Top)
handleModule (ModEval exp defs) = handleDefs defs (resolveExp exp)
