{-# LANGUAGE TupleSections #-}

-- Convert the concrete syntax into the syntax of miniTT.
module Concrete where

import Exp.Abs
import qualified MTT as A

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

defToNames :: Def -> [String]
defToNames (Def n _ _)     = [unIdent n]
defToNames (DefTDecl n _)  = [unIdent n]
defToNames (DefData n _ _) = [unIdent n]
defToNames (DefPrim defs)  = defsToNames defs

defsToNames :: [Def] -> [String]
defsToNames = nub . concatMap defToNames

-------------------------------------------------------------------------------
-- | Resolver and environment

-- local environment for variables and constructors
data Env = Env { constrs :: [String]
               }
         deriving (Eq, Show)

type Resolver a = ReaderT Env (StateT Integer (ErrorT String Identity)) a

emptyEnv :: Env
emptyEnv = Env [] []

runResolver :: Resolver a -> Either String a
runResolver x = runIdentity $ runErrorT $ evalStateT (runReaderT x emptyEnv) 0

insertConstrs :: [String] -> Env -> Env
insertConstrs cs e@Env{constrs = cs'} = e{constrs = cs ++ cs'}

getEnv :: Resolver Env
getEnv = ask

getConstrs :: Resolver [String]
getConstrs = getEnv >>= return . constrs

gensym :: Resolver Integer
gensym = do
  g <- lift get
  lift (modify succ)
  return g

lam :: Arg -> Resolver A.Exp -> Resolver A.Exp
lam a e = A.Lam (unArg a) <$> e

lams :: [Arg] -> Resolver A.Exp -> Resolver A.Exp
lams as e = foldr lam e as

resolveExp :: Exp -> Resolver A.Exp
resolveExp U            = return A.U
resolveExp Undef        = A.Undef <$> gensym
resolveExp Top          = return A.Top
resolveExp e@(App t s)  = do
  let x:xs = unApps e
  cs <- getConstrs
  if unVarBinder x `elem` cs
    then A.Con (unVarBinder x) <$> mapM resolveExp xs
    else A.App <$> resolveExp t <*> resolveExp s
resolveExp (Pi tele b)  = resolveTelePi (flattenTelePi tele) (resolveExp b)
resolveExp (Fun a b)    = A.Pi <$> resolveExp a <*> lam NoArg (resolveExp b)
resolveExp (Lam bs t)   = lams (map unBinder bs) (resolveExp t)
resolveExp (Split brs)  = A.Fun <$> gensym <*> mapM resolveBranch brs
resolveExp (Let defs e) = handleDefs defs (resolveExp e)
resolveExp (PN n)       = return (A.PN (unIdent n))
resolveExp (Var n)      = do
  let x = unArg n
  when (x == "_") (throwError "_ not a valid variable name")
  Env vs cs <- getEnv
  if x `elem` cs
    then return $ A.Con x []
    else  return $ A.Ref x

resolveWhere :: ExpWhere -> Resolver A.Exp
resolveWhere = resolveExp . unWhere

resolveBranch :: Branch -> Resolver (String,([String],A.Exp))
resolveBranch (Branch name args e) =
  (unIdent name,) <$> (unArgs args,) <*> resolveWhere e

-- Assumes a flattened telescope.
resolveTele :: [VDecl] -> Resolver [(String,A.Exp)]
resolveTele []                      = return []
resolveTele (VDecl [Binder a] t:ds) =
  (a,) <$> (resolveExp t <:> (resolveTele ds))
resolveTele ds                      =
  throwError $ "resolveTele: non flattened telescope " ++ show ds

-- Assumes a flattened telescope.
resolveTelePi :: [VDecl] -> Resolver A.Exp -> Resolver A.Exp
resolveTelePi [] b                      = b
resolveTelePi (VDecl [Binder x] a:as) b =
  A.Pi <$> resolveExp a <*> lam x (resolveTelePi as b)
resolveTelePi (t@(VDecl{}):as) _        =
  throwError ("resolveTelePi: non flattened telescope " ++ show t)

--------------------------------------------------------------------------------
-- | Call graph

callGraph :: [Def] -> [[[Def]]]
callGraph = filter (/= [[]]) . map flattenSCC . stronglyConnComp . graph

graph :: [Def] -> [([Def],String,[String])]
graph = map ((\(as,b:_,xs) -> (concat as,b,concat xs)) . unzip3)
      . groupBy ((==) `on` (\(_,n,_) -> n)) . concatMap defToGraph

defToGraph :: Def -> [([Def], String, [String])]
defToGraph d@(Def n args body) =
  [([d],unIdent n,freeVarsExp (unWhere body) \\ unArgs args)]
defToGraph d@(DefTDecl n exp)  = [([d],unIdent n,freeVarsExp exp)]
defToGraph d@(DefData n vdecls labels) =
  let iden = unIdent n
      fvB  = unions [ freeVarsTele tele \\ namesTele tele
                    | Sum _ tele <- labels ]
      x    = ([d],iden,freeVarsTele vdecls `union` fvB)
      xs   = [ ([],c,[iden]) | Sum (AIdent (_,c)) _ <- labels ]
  in x : xs
defToGraph (DefPrim defs) = graph (concatMap unfoldPrimitive defs)
  where
    unfoldPrimitive :: Def -> [Def]
    unfoldPrimitive d@(DefTDecl n a) = [d,Def n [] (NoWhere (PN n))]
    unfoldPrimitive d =
      error ("only type declarations are allowed in primitives " ++ show d)

freeVarsExp :: Exp -> [String]
freeVarsExp U           = []
freeVarsExp Undef       = []
freeVarsExp (Fun e1 e2) = freeVarsExp e1 `union` freeVarsExp e2
freeVarsExp (App e1 e2) = freeVarsExp e1 `union` freeVarsExp e2
freeVarsExp (Var x)     = [unArg x]
freeVarsExp (Lam bs e)  = freeVarsExp e \\ unArgsBinder bs
freeVarsExp (PN _)      = []
freeVarsExp (Let ds e)  =
  (freeVarsExp e `union` unions (map freeVarsDef ds)) \\ defsToNames ds
freeVarsExp (Split bs)  =
  unions [ unIdent bn : (freeVarsExp (unWhere e) \\ unArgs args)
         | Branch bn args e <- bs ]
freeVarsExp (Pi [] e)               = freeVarsExp e
freeVarsExp (Pi (PiDecl bs a:vs) e) =
  freeVarsExp a `union` (freeVarsExp (Pi vs e) \\
                         unArgs (map unVar (unApps bs)))

-- The free variables of the right hand side.
freeVarsDef :: Def -> [String]
freeVarsDef (Def _ args e)          = freeVarsExp (unWhere e) \\ unArgs args
freeVarsDef (DefTDecl _ e)          = freeVarsExp e
freeVarsDef (DefPrim defs)          = unions (map freeVarsDef defs)
freeVarsDef (DefData _ vdecls lbls) = freeVarsTele vdecls `union`
  (unions [ freeVarsTele vs | Sum _ vs <- lbls ] \\ namesTele vdecls)

freeVarsTele :: Tele -> [String]
freeVarsTele []              = []
freeVarsTele (VDecl bs e:ds) =
  freeVarsExp e `union` (freeVarsTele ds \\ unArgsBinder bs)

--------------------------------------------------------------------------------
-- | Handling mutual definitions

resolveLabel :: Sum -> Resolver (String,[(String,A.Exp)])
resolveLabel (Sum n tele) = (unIdent n,) <$> resolveTele (flattenTele tele)

handleMutual :: [[Def]] -> [String] -> Resolver [([String],(A.Exp,A.Exp))]
handleMutual []       _  = return []
handleMutual (ds:dss) ns = case sort ds of -- use Ord for Def: will put Def before DefTDecl
  [d@(DefData _ vdcls cs)]        -> do
    let flat   = flattenTele vdcls
    let args   = concatMap (\(VDecl binds _) -> map unBinder binds) flat
    let labels = A.Sum <$> gensym <*> mapM resolveLabel cs
    exp  <- local (insertNames ns) $ lams args labels
    typ  <- resolveTelePi flat (return A.U) -- data-decls. have type U
    rest <- handleMutual dss ns
    return ((ns,(exp,typ)):rest)
  [Def iden args body,DefTDecl _ t] -> do
    exp  <- local (insertNames ns) $ lams args (resolveWhere body)
    typ  <- resolveExp t
    rest <- handleMutual dss ns
    return ((ns,(exp,typ)):rest)
  x -> throwError $ "handleMutual: Something is missing or too many "
                  ++ "definition/declarations: " ++ show x

--                                         names  , exp : type
handleMutuals :: [[[Def]]] -> Resolver [[([String],(A.Exp,A.Exp))]]
handleMutuals []       = return []
handleMutuals (ds:dss) = do
  let ns = defsToNames $ concat ds
  handleMutual ds ns <:> local (insertNames ns) (handleMutuals dss)

handleLet :: A.Exp -> [[([String],(A.Exp,A.Exp))]] -> A.Exp
handleLet e []     = e
handleLet e (x:xs) = A.Def (handleLet e xs) es (concat nss)
  where (nss,es) = unzip x

handleDefs :: [Def] -> Resolver A.Exp -> Resolver A.Exp
handleDefs defs re = do
  let cg = callGraph defs
  let ns = defsToNames $ concat $ concat cg
  xs <- handleMutuals cg
  e  <- local (insertNames ns) re
  return (handleLet e xs)

handleModule :: Module -> Resolver A.Exp
handleModule (Module _ _ defs) = handleDefs defs (return A.Top)
