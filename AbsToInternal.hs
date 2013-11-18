{-# LANGUAGE PatternGuards #-}

-- Tranlates the terms of MiniTT into the Core terms.
module AbsToInternal where

import qualified Core as I
import Control.Monad.Error
import Control.Applicative
import MiniTT.MTT hiding (Error)

-- For an expression t, returns (u,ts) where u is no application
-- and t = u ts
unApps :: Exp -> (Exp,[Exp])
unApps (App r s) = let (t,ts) = unApps r in (t, s:ts)
unApps t         = (t,[])

translate :: Exp -> Either String I.Ter
translate t | PN n _ <- hd = translatePrimitive n ts
  -- First we try to handle primitive notions by looking whether the
  -- head term is a PN.
  where (hd,ts) = unApps t
translate (App r s) = I.App <$> translate r <*> translate s
translate (Pi a f) = I.Pi <$> translate a <*> translate f
translate (Lam t) = I.Lam <$> translate t
translate (Def e ts _) = -- ignores types for now
  I.Where <$> translate e <*> mapM translate ts
translate (Ref i) = return (I.Var i)
translate U = return I.U
translate (Con n ts) = I.Con n <$> mapM translate ts
translate (Fun bs) = I.Branch <$> mapM (\(n,b) -> do
                                           t <- translate b
                                           return (n,t)) bs
translate (Sum lbs) = I.LSum <$> mapM (\(n,ls) -> do
                                          ts <- mapM translate ls
                                          return (n,ts)) lbs
translate t = throwError ("translate: can not handle " ++ show t)

-- name, (arity for Exp, handler)
type PrimHandle = [(String, (Int, [Exp] -> Either String I.Ter))]

primHandle :: PrimHandle
primHandle =
  [ ("Id", (3, primId))
  , ("refl", (1, primRefl))
  , ("subst", (6, primSubst))
  , ("ext", (5, primExt))
  ]

-- TODO: Even though these can assume to have the right amount of
-- arguments, the pattern matching is pretty ugly... (?)
primId :: [Exp] -> Either String I.Ter
primId (a:x:y:[]) = I.Id <$> translate a <*> translate x <*> translate y

primRefl :: [Exp] -> Either String I.Ter
primRefl [x] = I.Refl <$> translate x

primSubst :: [Exp] -> Either String I.Ter
primSubst (a:c:x:y:eq:p:[]) =
  I.Trans <$> translate c <*> translate eq <*> translate p

primExt :: [Exp] -> Either String I.Ter
primExt (a:b:f:g:ptwise:[]) =
  I.Ext <$> translate b <*> translate f <*> translate g <*> translate p


-- Gets a name for a primitive notion, a list of arguments which might
-- be to long and returns the corresponding concept in the internal
-- syntax (Core).  Applies the rest of the terms if the list of terms
-- is longer than the arity.
translatePrimitive :: String -> [Exp] -> Either String I.Ter
translatePrimitive n ts = case lookup n primHandle of
  Just (arity,_) | length ts < arity ->
    throwError ("not enough arguments supplied to " ++ show n ++
                " PRIMITIVE (" ++ show arity ++ "arguments required)\n"
                ++"Arguments given: " ++ show ts)
  Just (arity,handler)               ->
    let (args,rest) = splitAt arity ts in
    manyApps <$> handler args <*> mapM translate rest
  Nothing                            ->
    throwError ("unknown PRIMITIVE: " ++ show n)

manyApps :: I.Ter -> [I.Ter] -> I.Ter
manyApps = foldl I.App
