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

type LEnv = [String]            -- local environment for variables

type Resolver = ReaderT LEnv (ErrorT String Identity)

runResolver :: Resolver a -> Either String a
runResolver x = runIdentity $ runErrorT $ runReaderT x []

-- resolveModule :: Module -> Resolver [(A.Exp,A.Exp)]
-- resolveModule (Module defs) = resolveMutualDefs defs

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
insertNames xs e = reverse xs ++ e -- TODO: ?????

unArg :: Arg -> String
unArg a = head $ insertVar a []

unArgs :: [Arg] -> [String]
unArgs = map unArg

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
resolveExp (Let defs e) = handleDefs defs (resolveExp e)
resolveExp (Con (AIdent (_,c)) es) = A.Con c <$> mapM resolveExp es
-- do
--   exp     <- resolveExp e       -- TODO: e should know about the definitions!
--   exptyps <- resolveMutualDefs defs
--   let (exps,typs) = unzip exptyps
--   return (A.Def exp exps typs)

unWhere :: ExpWhere -> Exp
unWhere (Where e ds) = Let ds e
unWhere (NoWhere e)  = e

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
  (:) <$> resolveExp t <*> local (insertVar a) (resolveTele ds)
resolveTele ds =
  throwError ("resolveTele: non flattened telescope " ++ show ds)

resolveLabel :: Sum -> Resolver (String,[A.Exp])
resolveLabel (Sum (AIdent (_,name)) (Tele tele)) =
  resolveTele (flattenTele tele) >>= \ts -> return (name, ts)

-- -- -- Anders: Also output a list of constructor names
-- unData :: Def -> Resolver (AIdent,[Arg],A.Exp,A.Exp)
-- unData (DefData iden (Tele vdcls) cs) = do
--   let flat = flattenTele vdcls
--   let args = concatMap (\(VDecl binds _) -> map unBinder binds) flat
--   let cons = [ Arg id | Sum id _ <- cs ]
--   let labels = A.Sum <$> mapM (local (insertVars args) . resolveLabel) cs
--   -- Anders: I think we should add the name of the data type when resolving
--   --         the sums.
--   exp <- resolveLams (Arg iden : args) labels
--   typ <- resolveTelePi flat (return A.U) -- data-decls. have value type U
--   return (iden,cons,exp,typ)
-- unData def = throwError ("unData: data declaration expected " ++ show def)

-- All the defs are mutual.
-- TODO: optimize with call-graph. Then the result type should be
-- Resolver Env instead (or Resolver [Env] ?).
-- resolveMutualDefs :: [Def] -> Resolver [(A.Exp,A.Exp)]
-- resolveMutualDefs []         = return []
-- resolveMutualDefs (def:defs) = case def of -- TODO: code-duplication (last 2 cases)
--   DefData{} -> do
--     (iden,args,exp,typ) <- unData def
--     -- Anders: Now that the constructor names are known we can add them
--     rest <- local (insertVars (Arg iden : args)) (resolveMutualDefs defs)
--     return ((exp,typ):rest)
--   DefTDecl iden t -> do
--     (Def _ args body,defs') <- findDef iden defs
--     exp <- resolveLams args (local (insertVars args) (resolveExpWhere body))
--     typ <- resolveExp t
--     rest <- local (insertVar (Arg iden)) (resolveMutualDefs defs')
--     return ((exp,typ):rest)
--   Def iden args body -> do
--     (DefTDecl _ t, defs') <- findTDecl iden defs
--     -- TODO: There is a bug here for recursive definitions!
--     --exp <- resolveLams args (resolveExpWhere body)
--     exp <- resolveLams args (local (insertVars args) (resolveExpWhere body))
--     typ <- resolveExp t
--     rest <- local (insertVar (Arg iden)) (resolveMutualDefs defs')
--     return ((exp,typ):rest)
--   where
--     -- pick out a definition
--     findDef :: AIdent -> [Def] -> Resolver (Def,[Def])
--     findDef iden []         =
--       throwError (show iden ++ " is lacking an accompanying binding")
--     findDef iden@(AIdent (_,name)) (def:defs) = case def of
--       Def (AIdent (_,name')) _ _ | name == name' -> return (def,defs)
--       _                                              ->
--         findDef iden defs >>= \(d,ds) -> return (d, def:ds)

--     -- pick out a type declaration
--     findTDecl :: AIdent -> [Def] -> Resolver (Def,[Def])
--     findTDecl iden []         =
--       throwError (show iden ++ " is lacking an accompanying type declaration")
--     findTDecl iden@(AIdent (_,name)) (def:defs) = case def of
--       DefTDecl (AIdent (_,name')) _ | name == name' -> return (def,defs)
--       _                                                 ->
--         findTDecl iden defs >>= \(d,ds) -> return (d, def:ds)

--------------------------------------------------------------------------------
-- Call graph

callGraph :: [Def] -> [[[Def]]]
callGraph = filter (/= [[]]) . map flattenSCC . stronglyConnComp . graph 

-- TODO: Clean?
graph :: [Def] -> [([Def],String,[String])]
graph = map ((\(as,b:_,xs) -> (concat as,b,concat xs)) . unzip3) 
      . groupBy ((==) `on` (\(_,n,_) -> n)) . concatMap defToGraph

defToGraph :: Def -> [([Def], String, [String])]
defToGraph d = case d of
  (Def (AIdent (_,iden)) args body) ->
    [([d],iden,freeVars (unWhere body) \\ unArgs args)]
  (DefTDecl (AIdent (_,iden)) exp) -> [([d],iden,freeVars exp)]
  (DefData (AIdent (_,iden)) (Tele vdecls) labels) ->
       [ ([d],iden,freeVarsTele vdecls `union` fvB) ]
    ++ [ ([],c,[iden]) | Sum (AIdent (_,c)) _ <- labels ] 
    where fvB = unions [ freeVarsTele tele \\ namesTele tele 
                       | Sum _ (Tele tele) <- labels ]

freeVars :: Exp -> [String]
freeVars (Let ds e)  = (freeVars e `union` unions (map freeVarsDef ds))
                       \\ defsToNames ds
freeVars (Lam bs e)  = freeVars e \\ unArgs (map unBinder bs)
freeVars (Case e bs) =
  freeVars e `union` unions [ str:(freeVars (unWhere e) \\ unArgs args)
                            | Branch (AIdent (_,str)) args e <- bs ]
freeVars (Fun e1 e2) = freeVars e1 `union` freeVars e2
freeVars (Pi (TeleNE []) e) = freeVars e
freeVars (Pi (TeleNE (VDeclNE (VDecl bs a):vs)) e) =
  freeVars a `union` (freeVars (Pi (TeleNE vs) e) \\ unArgs (map unBinder bs))
freeVars (App e1 e2) = freeVars e1 `union` freeVars e2
freeVars (Var x)     = [unArg (unBinder x)]
freeVars U           = []
freeVars (Con _ es)  = unions (map freeVars es)

-- The free variables of the right hand side.
freeVarsDef :: Def -> [String]
freeVarsDef (Def _ args exp) = freeVars (unWhere exp) \\ unArgs args
freeVarsDef (DefTDecl _ exp) = freeVars exp
freeVarsDef (DefData _ (Tele vdecls) labels) = freeVarsTele vdecls `union`
  (unions [ freeVarsTele vs | Sum _ (Tele vs) <- labels ] \\ namesTele vdecls)

freeVarsTele :: [VDecl] -> [String]
freeVarsTele []                = []
freeVarsTele ((VDecl bs e):ds) =
  freeVars e `union` (freeVarsTele ds \\ unArgs (map unBinder bs))

namesTele :: [VDecl] -> [String]
namesTele vs = unions [ unArgs (map unBinder args) | VDecl args _ <- vs ]

defToName :: Def -> String
defToName (Def (AIdent (_,n)) _ _)     = n
defToName (DefTDecl (AIdent (_,n)) _)  = n
defToName (DefData (AIdent (_,n)) _ _) = n

defsToNames :: [Def] -> [String]
defsToNames = nub . map defToName

unions :: Eq a => [[a]] -> [a]
unions = foldr union []

--------------------------------------------------------------------------------
-- 
-- rmDefs :: [Either [Def] (Def,Def)]

-- resolveMutualDefs :: [Def] -> Resolver [(A.Exp,A.Exp)]
-- resolveMutualDefs []         = return []
-- resolveMutualDefs (def:defs) = case def of -- TODO: code-duplication (last 2 cases)
--   DefData{} -> do
--     (iden,args,exp,typ) <- unData def
--     -- Anders: Now that the constructor names are known we can add them
--     rest <- local (insertVars (Arg iden : args)) (resolveMutualDefs defs)
--     return ((exp,typ):rest)
--   DefTDecl iden t -> do
--     (Def _ args body,defs') <- findDef iden defs
--     exp <- resolveLams args (local (insertVars args) (resolveExpWhere body))
--     typ <- resolveExp t
--     rest <- local (insertVar (Arg iden)) (resolveMutualDefs defs')
--     return ((exp,typ):rest)
--   Def iden args body -> do
--     (DefTDecl _ t, defs') <- findTDecl iden defs
--     -- TODO: There is a bug here for recursive definitions!
--     --exp <- resolveLams args (resolveExpWhere body)
--     exp <- resolveLams args (local (insertVars args) (resolveExpWhere body))
--     typ <- resolveExp t
--     rest <- local (insertVar (Arg iden)) (resolveMutualDefs defs')
--     return ((exp,typ):rest)

-- -- -- Anders: Also output a list of constructor names
unData' :: Def -> [String] -> Resolver (A.Exp,A.Exp)
unData' (DefData _ (Tele vdcls) cs) ns = do
  let flat = flattenTele vdcls
  let args = concatMap (\(VDecl binds _) -> map unBinder binds) flat
--   let cons = [ Arg id | Sum id _ <- cs ]
  let labels = A.Sum <$> mapM (local (insertVars args . insertNames ns) . resolveLabel) cs
  exp <- resolveLams args labels
  typ <- resolveTelePi flat (return A.U) -- data-decls. have value type U
  return (exp,typ)
unData' def _ = throwError ("unData: data declaration expected " ++ show def)

handleMutual :: [[Def]] -> [String] -> Resolver [(A.Exp,A.Exp)]
handleMutual []       _  = return []
handleMutual (ds:dss) ns = case sort ds of -- use Ord on for Def: will put Def before DefTDecl
  [d@DefData{}]        -> do
    (exp,typ) <- unData' d ns
    rest <- handleMutual dss ns
    return ((exp,typ):rest)
  [Def iden args body,DefTDecl _ t] -> do
    exp <- local (insertNames ns) $ resolveLams args (local (insertVars args) (resolveExpWhere body))
    typ <- resolveExp t
    rest <- handleMutual dss ns
    return ((exp,typ):rest)
  x -> throwError $ "handleMutual: Something is missing or too many definition/declarations: " ++ show x

--                                         exp : type
handleMutuals :: [[[Def]]] -> Resolver [[(A.Exp,A.Exp)]]
handleMutuals [] = return []
handleMutuals (ds:dss) = do
  let ns = defsToNames $ concat ds
--  xs <- local (insertNames ns) $ handleMutual ds
  xs <- handleMutual ds ns
  (xs :) <$> local (insertNames ns) (handleMutuals dss)

handleLet :: A.Exp -> [[(A.Exp,A.Exp)]] -> A.Exp
handleLet e []     = e
handleLet e (x:xs) = A.Def (handleLet e xs) es ts
  where (es,ts) = unzip x

handleDefs :: [Def] -> Resolver A.Exp -> Resolver A.Exp
handleDefs defs re = do 
  let cg = callGraph defs
  let ns = defsToNames $ concat $ concat cg
  xs <- handleMutuals cg
  e  <- local (insertNames ns) re
  return (handleLet e xs)

handleModule :: Module -> Resolver A.Exp
handleModule (Module defs) = handleDefs defs (return A.Top)



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
