{-# LANGUAGE TupleSections #-}
-- Tranlates the terms of MiniTT into the Core terms.
module AbsToInternal where

import qualified Core as I
import Control.Monad.Error
import Control.Applicative
import Control.Arrow
import MTT hiding (Error)

-- For an expression t, returns (u,ts) where u is no application
-- and t = u ts
unApps :: Exp -> (Exp,[Exp])
unApps (App r s) = let (t,ts) = unApps r in (t, s:ts)
unApps t         = (t,[])

translate :: Exp -> Either String I.Ter
translate (PN n) = -- translatePrimitive n []
  return $ I.PN n
--  throwError $ "No primitive expected: " ++ show n
translate t@(App _ _) = let (hd,rest) = unApps t in case hd of
  Ref n | n `elem` reservedNames -> translatePrimitive n rest
  _ -> manyApps <$> translate hd <*> mapM translate rest
translate (Pi a f) = I.Pi <$> translate a <*> translate f
translate (Lam x t) = I.Lam x <$> translate t
translate (Def e (_,ts)) = -- ignores types for now
  I.Where <$> translate e <*> mapM (\(n,e') -> do
                                       t <- translate e'
                                       return (n,t)) ts
translate (Ref n) = return (I.Var n)
translate U = return I.U
translate (Con n ts) = I.Con n <$> mapM translate ts
translate (Fun bs) = I.Branch <$> mapM (\(n,(ns,b)) -> do
                                           t <- translate b
                                           return (n,(ns,t))) bs
translate (Sum lbs) = I.LSum <$> mapM (\(n,tele) -> do
                                          ts <- mapM (\(n',e') -> (n',) <$> translate e') tele
                                          --let ts' = lambdaTele ts
                                          return (n,ts)) lbs
translate t = throwError ("translate: can not handle " ++ show t)

-- name, (arity for Exp, handler)
type PrimHandle = [(String, (Int, [Exp] -> Either String I.Ter))]

primHandle :: PrimHandle
primHandle =
  [ ("Id",            (3, primId))
  , ("refl",          (2, primRefl))
  , ("subst",         (6, primSubst)) -- TODO: remove, better only J
  , ("substInv",      (6, primSubstInv)) -- TODO: remove
  , ("ext",           (5, primExt))
  , ("J",             (6, primJ))
  , ("Jeq",           (4, primJeq))
  , ("inh",           (1, primInh))
  , ("inc",           (2, primInc))
  , ("squash",        (3, primSquash))
  , ("inhrec",        (5, primInhRec))
  , ("equivEq",       (5, primEquivEq))
  , ("transport",     (4, primTransport))
  , ("transportRef",  (2, primTransportRef))
  , ("equivEqRef",    (3, primEquivEqRef))
  , ("transpEquivEq", (6, primTransUEquivEq))
  ]

reservedNames :: [String]
reservedNames = map fst primHandle

-- TODO: Even though these can assume to have the right amount of
-- arguments, the pattern matching is pretty ugly... (?)
primId :: [Exp] -> Either String I.Ter
primId [a,x,y] = I.Id <$> translate a <*> translate x <*> translate y

primRefl :: [Exp] -> Either String I.Ter
primRefl [a,x] = I.Refl <$> translate x

primSubst :: [Exp] -> Either String I.Ter
primSubst [a,c,x,y,eq,p] =
  I.Trans <$> translate c <*> translate eq <*> translate p

primSubstInv :: [Exp] -> Either String I.Ter
primSubstInv [a,c,x,y,eq,p] =
  I.TransInv <$> translate c <*> translate eq <*> translate p

primExt :: [Exp] -> Either String I.Ter
primExt [a,b,f,g,ptwise] =
  I.Ext <$> translate b <*> translate f <*> translate g <*> translate ptwise

primJ :: [Exp] -> Either String I.Ter
primJ [a,u,c,w,v,p] =
  I.J <$> translate a <*> translate u <*> translate c
      <*> translate w <*> translate v <*> translate p

primJeq :: [Exp] -> Either String I.Ter
primJeq [a,u,c,w] =
  I.JEq <$> translate a <*> translate u <*> translate c <*> translate w

primInh :: [Exp] -> Either String I.Ter
primInh [a] = I.Inh <$> translate a

primInc :: [Exp] -> Either String I.Ter
primInc [a,x] = I.Inc <$> translate x

primSquash :: [Exp] -> Either String I.Ter
primSquash [a,x,y] = I.Squash <$> translate x <*> translate y

primInhRec :: [Exp] -> Either String I.Ter
primInhRec [a,b,p,f,x] =
  I.InhRec <$> translate b <*> translate p <*> translate f <*> translate x

primEquivEq :: [Exp] -> Either String I.Ter
primEquivEq [a,b,f,s,t] =
  I.EquivEq <$> translate a <*> translate b <*> translate f
            <*> translate s <*> translate t


primTransport :: [Exp] -> Either String I.Ter
primTransport [a,b,p,x] = I.TransU <$> translate p <*> translate x

primTransportRef :: [Exp] -> Either String I.Ter
primTransportRef [a,x] = I.TransURef <$> translate x

-- (A:U) -> (s: (y:A) -> pathTo A a) -> (t : (y:B) -> (v:pathTo A a) -> Id (path To A a) (s y) v) ->
-- Id (Id U A A) (refl U A) (equivEq A A (id A) s t)
primEquivEqRef :: [Exp] -> Either String I.Ter
primEquivEqRef [a,s,t] = I.EquivEqRef <$> translate a <*> translate s <*> translate t

-- (A B : U) -> (f : A -> B) (s:(y:B) -> fiber A B f y) -> (t : (y:B) -> (v:fiber A B f y) -> Id (fiber A B f y) (s y) v) ->
-- (a : A) -> Id B (f a) (transport A B (equivEq A B f s t) a)
primTransUEquivEq :: [Exp] -> Either String I.Ter
primTransUEquivEq [a,b,f,s,t,x] =
  I.TransUEquivEq <$> translate a <*> translate b <*> translate f <*>
                      translate s <*> translate t <*> translate x


manyLams :: [Binder] -> I.Ter -> I.Ter
manyLams [] t = t
manyLams (b:bs) t = I.Lam b (manyLams bs t)

-- Gets a name for a primitive notion, a list of arguments which might
-- be to long and returns the corresponding concept in the internal
-- syntax (Core).  Applies the rest of the terms if the list of terms
-- is longer than the arity.
translatePrimitive :: String -> [Exp] -> Either String I.Ter
translatePrimitive n ts = case lookup n primHandle of
  Just (arity,_) | length ts < arity ->
    let r = arity - length ts
        binders = map (\n -> "_" ++ show n) [1..r]
        vars = map Ref binders
    in
     manyLams binders <$> translatePrimitive n (ts ++ vars)
    -- throwError ("not enough arguments supplied to " ++ show n ++
    --             " primitive (" ++ show arity ++ " arguments required)\n"
    --             ++ "Arguments given: " ++ show ts)

  Just (arity,handler)               ->
    let (args,rest) = splitAt arity ts in
    manyApps <$> handler args <*> mapM translate rest
  Nothing                            ->
    throwError ("unknown primitive: " ++ show n)

manyApps :: I.Ter -> [I.Ter] -> I.Ter
manyApps = foldl I.App

