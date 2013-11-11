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

type Resolver a = ReaderT LEnv (ErrorT String Identity) a

runResolver :: Resolver a -> a
runResolver x = case runIdentity $ runErrorT $ runReaderT x [] of
  Left e -> error e
  Right a -> a


-- not needed anymore?
-- -- Note that the grammar guarantees that as is nonempty.
-- resolveVars :: [A.Args] -> Resolver Exp
-- resolveVars []  = throwError "empty binder"
-- resolveVars as = foldl1 (liftA2 App) (map resolveVar as)


look :: A.AIdent -> Resolver Exp
look iden@(A.AIdent (_, str)) = do
  e <- ask
  case elemIndex str e of
    Just n  -> return $ Ref n
    Nothing -> throwError ("unknown identifier: " ++ show iden)

-- Insert a variable in an environment.
insertVar :: A.Args -> LEnv -> LEnv
insertVar (A.Arg (A.AIdent (_,str))) e = str:e
insertVar A.NoArg                    e = "_":e

-- A dummy variable we can insert when we have to lift an
-- environment.
dummyVar :: A.Args
dummyVar = A.NoArg

resolveVar :: A.Args -> Resolver Exp
resolveVar (A.Arg i) = look i
resolveVar A.NoArg   = throwError "_ not a valid variable name "

unNE :: A.VDeclNE -> A.VDecl
unNE (A.VDeclNE vdcl) = vdcl

unBinder :: A.Binder -> A.Args
unBinder (A.Binder b) = b

-- Flatten a telescope, e.g., flatten (a b : A) (c : C) into
-- (a : A) (b : A) (c:C).
flattenTele :: [A.VDecl] -> [A.VDecl]
flattenTele = concatMap $ \(A.VDecl bs e) -> [A.VDecl [b] e | b <- bs]

-- Assumes the telescope is flattened.
resolveTelePi :: [A.VDecl] -> A.Exp -> Resolver Exp
resolveTelePi [] b = resolveExp b
resolveTelePi ((A.VDecl [A.Binder x] a):as) b =
  Pi <$> resolveExp a <*> (Lam <$> local (insertVar x) (resolveTelePi as b))
resolveTelePi (t@(A.VDecl _ _):as) _ =
  throwError ("resolveTelePi: non flattened telescope " ++ show t)

resolveLams :: [A.Args] -> A.Exp -> Resolver Exp
resolveLams [] t = resolveExp t
resolveLams (a:as) t = Lam <$> local (insertVar a) (resolveLams as t)

resolveExp :: A.Exp -> Resolver Exp
resolveExp A.U = return U
resolveExp (A.Var (A.Binder a)) = resolveVar a
resolveExp (A.App t s) = App <$> resolveExp t <*> resolveExp s
resolveExp (A.Pi (A.TeleNE tele) b) =
  resolveTelePi (flattenTele (map unNE tele)) b
resolveExp (A.Fun a b) =
  Pi <$> resolveExp a <*> (Lam <$> local (insertVar dummyVar) (resolveExp b))
resolveExp (A.Lam bs t) = resolveLams (map unBinder bs) t
resolveExp (A.Case e brs) = undefined
resolveExp (A.Let defs e) = undefined
resolveExp (A.Where e defs) = undefined

{-
type TypedEnv = [(Exp,Exp)] -- each entry comes with its type

resolveDef :: A.Def -> Resolver TypedEnv
resolveDef = undefined
resolveDefs :: [A.Def] -> Resolver TypedEnv
resolveDefs = undefined
-}

