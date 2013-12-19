{-# LANGUAGE TupleSections #-}
-- Tranlates the terms of MiniTT into the cubical syntax.
module MTTtoCTT where

import qualified CTT as I
import Control.Monad.Error
import Control.Applicative
import Control.Arrow
import MTT

-- For an expression t, returns (u,ts) where u is no application
-- and t = u ts
unApps :: Exp -> (Exp,[Exp])
unApps (App r s) = let (t,ts) = unApps r in (t, ts ++ [s])
unApps t         = (t,[])

apps :: I.Ter -> [I.Ter] -> I.Ter
apps = foldl I.App

lams :: [String] -> I.Ter -> I.Ter
lams bs t = foldr I.Lam t bs

translate :: Exp -> Either String I.Ter
translate U              = return I.U
translate (Undef prim)   = return $ I.Undef prim
translate (Lam x t)      = I.Lam x <$> translate t
translate (Pi a f)       = I.Pi <$> translate a <*> translate f
translate t@(App _ _)    =
  let (hd,rest) = unApps t
  in case hd of
    Var n | n `elem` reservedNames -> translatePrimitive n rest
    _ -> apps <$> translate hd <*> mapM translate rest
translate (Def e (_,ts)) = -- ignores types for now
  I.Where <$> translate e <*> mapM (\(n,e') -> (n,) <$> translate e') ts
translate (Var n) | n `elem` reservedNames = translatePrimitive n []
                  | otherwise              = return (I.Var n)
translate (Con n ts)     = I.Con n <$> mapM translate ts
translate (Fun pr bs)    =
  I.Branch pr <$> mapM (\(n,(ns,b)) -> (n,) <$> (ns,) <$> translate b) bs
translate (Sum pr lbs)   =
  I.LSum pr <$> sequence [ (n,) <$> mapM (\(n',e') -> (n',) <$> translate e') tl
                         | (n,tl) <- lbs ]
translate t              = throwError $ "translate: can not handle " ++ show t

-- Gets a name for a primitive notion, a list of arguments which might be too
-- long and returns the corresponding concept in the internal syntax. Applies
-- the rest of the terms if the list of terms is longer than the arity.
translatePrimitive :: String -> [Exp] -> Either String I.Ter
translatePrimitive n ts = case lookup n primHandle of
  Just (arity,_) | length ts < arity ->
    let r       = arity - length ts
        binders = map (\n -> '_' : show n) [1..r]
        vars    = map Var binders
    in lams binders <$> translatePrimitive n (ts ++ vars)
  Just (arity,handler)               ->
    let (args,rest) = splitAt arity ts
    in apps <$> handler args <*> mapM translate rest
  Nothing                            ->
    throwError ("unknown primitive: " ++ show n)

-- | Primitive notions

-- name, (arity for Exp, handler)
type PrimHandle = [(String, (Int, [Exp] -> Either String I.Ter))]

primHandle :: PrimHandle
primHandle =
  [ ("Id",            (3, primId))
  , ("refl",          (2, primRefl))
  , ("funExt",        (5, primExt))
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

primId :: [Exp] -> Either String I.Ter
primId [a,x,y] = I.Id <$> translate a <*> translate x <*> translate y

primRefl :: [Exp] -> Either String I.Ter
primRefl [a,x] = I.Refl <$> translate x

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

primEquivEqRef :: [Exp] -> Either String I.Ter
primEquivEqRef [a,s,t] = I.EquivEqRef <$> translate a <*> translate s <*> translate t

primTransUEquivEq :: [Exp] -> Either String I.Ter
primTransUEquivEq [a,b,f,s,t,x] =
  I.TransUEquivEq <$> translate a <*> translate b <*> translate f
                  <*> translate s <*> translate t <*> translate x