{-# LANGUAGE PatternGuards #-}

-- Tranlates the terms of MiniTT into the Core terms.
module AbsToInternal where

import qualified Core as I
import Control.Monad.Error
import Control.Applicative
import MTT hiding (Error)

import Debug.Trace

-- For an expression t, returns (u,ts) where u is no application
-- and t = u ts
unApps :: Exp -> (Exp,[Exp])
unApps (App r s) = let (t,ts) = unApps r in (t, s:ts)
unApps t         = (t,[])


numberOfPis :: Exp -> Int
numberOfPis (Pi a (Lam b)) = 1 + numberOfPis b
numberOfPis _              = 0

-- etaPN :: Int -> I.Ter -> I.Ter
-- etaPN 0 t = t
-- etaPN n t = I.Lam $ etaPN (n-1) (I.App t (I.Var (n-1)))

manyLams :: Int -> I.Ter -> I.Ter
manyLams 0 t = t
manyLams n t = I.Lam (manyLams (n-1) t)

-- lambdaTele :: [I.Ter] -> [I.Ter]
-- lambdaTele [] = []
-- lambdaTele (t:ts) = t : map I.Lam (lambdaTele ts)

translate :: Exp -> Either String I.Ter
-- translate t | PN n _ <- hd = translatePrimitive n ts
--   -- First we try to handle primitive notions by looking whether the
--   -- head term is a PN.
--   where (hd,ts) = unApps t
translate (PN n a) = manyLams i <$> translatePrimitive n vars -- eta expand PNs
  where i = numberOfPis a
        vars = map Ref [i-1,i-2..0]
translate (App r s) = I.App <$> translate r <*> translate s
translate (Pi a f) = I.Pi <$> translate a <*> translate f
translate (Lam t) = I.Lam <$> translate t
translate (Def e ts _ _) = -- ignores types for now
  I.Where <$> translate e <*> mapM translate ts
translate (Ref i) = return (I.Var i)
translate U = return I.U
translate (Con n ts) = I.Con n <$> mapM translate ts
translate (Fun bs) = I.Branch <$> mapM (\(n,b) -> do
                                           t <- translate b
                                           return (n,t)) bs
translate (Sum lbs) = I.LSum <$> mapM (\(n,ls) -> do
                                          ts <- mapM translate ls
                                          --let ts' = lambdaTele ts
                                          return (n,ts)) lbs
translate t = throwError ("translate: can not handle " ++ show t)

-- name, (arity for Exp, handler)
type PrimHandle = [(String, (Int, [Exp] -> Either String I.Ter))]

primHandle :: PrimHandle
primHandle =
  [ ("Id",    (3, primId))
  , ("refl",  (2, primRefl))
  , ("subst", (6, primSubst)) -- TODO: remove, better only J
  , ("ext",   (5, primExt))
  , ("J",     (6, primJ))
  , ("Jeq",   (4, primJeq))
  , ("inh",   (1, primInh))
  , ("inc",   (2, primInc))
  , ("squash",(3, primSquash))
  , ("inhrec",(5, primInhRec))
  , ("equivEq", (5, primEquivEq))
  ]

-- TODO: Even though these can assume to have the right amount of
-- arguments, the pattern matching is pretty ugly... (?)
primId :: [Exp] -> Either String I.Ter
primId [a,x,y] = I.Id <$> translate a <*> translate x <*> translate y

primRefl :: [Exp] -> Either String I.Ter
primRefl [a,x] = I.Refl <$> translate x

primSubst :: [Exp] -> Either String I.Ter
primSubst [a,c,x,y,eq,p] =
  I.Trans <$> translate c <*> translate eq <*> translate p

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

-- Gets a name for a primitive notion, a list of arguments which might
-- be to long and returns the corresponding concept in the internal
-- syntax (Core).  Applies the rest of the terms if the list of terms
-- is longer than the arity.
translatePrimitive :: String -> [Exp] -> Either String I.Ter
translatePrimitive n ts = case lookup n primHandle of
  Just (arity,_) | length ts < arity ->
    throwError ("not enough arguments supplied to " ++ show n ++
                " primitive (" ++ show arity ++ " arguments required)\n"
                ++ "Arguments given: " ++ show ts)
  Just (arity,handler)               ->
    let (args,rest) = splitAt arity ts in
    manyApps <$> handler args <*> mapM translate rest
  Nothing                            ->
    throwError ("unknown primitive: " ++ show n)

manyApps :: I.Ter -> [I.Ter] -> I.Ter
manyApps = foldl I.App
