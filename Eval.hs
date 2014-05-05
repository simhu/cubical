{-# LANGUAGE TupleSections #-}
module Eval where

import Control.Applicative
import Control.Arrow (second)
import Control.Monad
import Control.Monad.Reader
import Data.Functor.Identity
import Data.List
import Data.Maybe (fromMaybe)

import CTT

look :: Ident -> Env -> (Binder, Val)
look x (Pair rho (n@(y,l),u))
  | x == y    = (n, u)
  | otherwise = look x rho
look x r@(PDef es r1) = case lookupIdent x es of
  Just (y,t)  -> (y,eval r t)
  Nothing     -> look x r1

eval :: Env -> Ter -> Val
eval e U               = VU
eval e (App r s)       = app (eval e r) (eval e s)
eval e (Var i)         = snd (look i e)
eval e (Pi a b)        = VPi (eval e a) (eval e b)
eval e (Lam x t)       = Ter (Lam x t) e -- stop at lambdas
eval e (Sigma a b)     = VSigma (eval e a) (eval e b)
eval e (SPair a b)     = VSPair (eval e a) (eval e b)
eval e (Fst a)         = fstSVal (eval e a)
eval e (Snd a)         = sndSVal (eval e a)
eval e (Where t decls) = eval (PDef [ (x,y) | (x,_,y) <- decls ] e) t
eval e (Con name ts)   = VCon name (map (eval e) ts)
eval e (Split pr alts) = Ter (Split pr alts) e
eval e (Sum pr ntss)   = Ter (Sum pr ntss) e
eval e (Undef _)       = error "undefined"

evals :: Env -> [(Binder,Ter)] -> [(Binder,Val)]
evals env = map (second (eval env))

app :: Val -> Val -> Val
app (Ter (Lam x t) e) u                         = eval (Pair e (x,u)) t
app (Ter (Split _ nvs) e) (VCon name us) = case lookup name nvs of
    Just (xs,t)  -> eval (upds e (zip xs us)) t
    Nothing -> error $ "app: Split with insufficient arguments; " ++
                        "missing case for " ++ name
app u@(Ter (Split _ _) _) v
  | isNeutral v = VSplit u v -- v should be neutral
  | otherwise   = error $ "app: (VSplit) " ++ show v ++ " is not neutral"
app r s
  | isNeutral r = VApp r s -- r should be neutral
  | otherwise   = error $ "app: (VApp) " ++ show r ++ " is not neutral"


fstSVal, sndSVal :: Val -> Val
fstSVal (VSPair a b)    = a
fstSVal u | isNeutral u = VFst u
          | otherwise   = error $ show u ++ " should be neutral"
sndSVal (VSPair a b)    = b
sndSVal u | isNeutral u = VSnd u
          | otherwise   = error $ show u ++ " should be neutral"

-- apps :: Val -> [Val] -> Eval Val
-- apps = foldM app

-- appName :: Val -> Name -> Eval Val
-- appName (Path x u) y | y `elem` [0,1] = u `face` (x,y)
-- appName p y          | y `elem` [0,1] = return $ VAppName p y
--                                         -- p has to be neutral
-- appName (Path x u) y | x == y             = return u
--                      | y `elem` support u = error ("appName " ++ "\nu = " ++
--                                                    show u ++ "\ny = " ++ show y)
--                      | otherwise          = return $ swap u x y
-- appName v y          = return $ VAppName v y

-- -- Compute the face of an environment
-- faceEnv :: OEnv -> Side -> Eval OEnv
-- faceEnv e xd = mapOEnvM (`face` xd) e

-- faceName :: Name -> Side -> Name
-- faceName 0 _                 = 0
-- faceName 1 _                 = 1
-- faceName x (y,d) | x == y    = d
--                  | otherwise = x

-- -- Compute the face of a value
-- face :: Val -> Side -> Eval Val
-- face u xdir@(x,dir) =
--   let fc v = v `face` xdir in case u of
--   VU          -> return VU
--   Ter t e -> do e' <- e `faceEnv` xdir
--                 eval e' t
--   VId a v0 v1 -> VId <$> fc a <*> fc v0 <*> fc v1
--   Path y v | x == y    -> return u
--            | otherwise -> Path y <$> fc v
--   -- VExt y b f g p | x == y && dir == down -> return f
--   --                | x == y && dir == up   -> return g
--   --                | otherwise             ->
--   --                  VExt y <$> fc b <*> fc f <*> fc g <*> fc p
--   VHExt y b f g p | x == y && dir == down -> return f
--                   | x == y && dir == up   -> return g
--                   | otherwise             ->
--                     VHExt y <$> fc b <*> fc f <*> fc g <*> fc p
--   VPi a f    -> VPi <$> fc a <*> fc f
--   VSigma a f -> VSigma <$> fc a <*> fc f
--   VSPair a b -> VSPair <$> fc a <*> fc b
--   VInh v     -> VInh <$> fc v
--   VInc v     -> VInc <$> fc v
--   VSquash y v0 v1 | x == y && dir == down -> return v0
--                   | x == y && dir == up   -> return v1
--                   | otherwise             -> VSquash y <$> fc v0 <*> fc v1
--   VCon c us -> VCon c <$> mapM fc us
--   VEquivEq y a b f s t | x == y && dir == down -> return a
--                        | x == y && dir == up   -> return b
--                        | otherwise             ->
--                          VEquivEq y <$> fc a <*> fc b <*> fc f <*> fc s <*> fc t
--   VPair y a v | x == y && dir == down -> return a
--               | x == y && dir == up   -> fc v
--               | otherwise             -> VPair y <$> fc a <*> fc v
--   VEquivSquare y z a s t | x == y                -> return a
--                          | x == z && dir == down -> return a
--                          | x == z && dir == up   -> do
--                            let idV = Ter (Lam (noLoc "x") (Var "x")) oEmpty
--                            return $ VEquivEq y a a idV s t
--                          | otherwise             ->
--                           VEquivSquare y z <$> fc a <*> fc s <*> fc t
--   VSquare y z v | x == y                -> fc v
--                 | x == z && dir == down -> fc v
--                 | x == z && dir == up   -> do
--                   v' <- fc v
--                   VPair y <$> v' `face` (y,down) <*> pure v'
--                 | otherwise             -> VSquare y z <$> fc v
--   Kan Fill a b@(Box dir' y v nvs)
--     | x /= y && x `notElem` nonPrincipal b -> fillM (fc a) (mapBoxM fc b)
--     | x `elem` nonPrincipal b              -> return $ lookBox (x,dir) b
--     | x == y && dir == mirror dir'         -> return v
--     | otherwise                            -> com a b
--   VFillN a b@(Box dir' y v nvs)
--     | x /= y && x `notElem` nonPrincipal b -> fillM (fc a) (mapBoxM fc b)
--     | x `elem` nonPrincipal b              -> return $ lookBox (x,dir) b
--     | x == y && dir == mirror dir'         -> return v
--     | otherwise                            -> com a b
--   Kan Com a b@(Box dir' y v nvs)
--     | x == y                     -> return u
--     | x `notElem` nonPrincipal b -> comM (fc a) (mapBoxM fc b)
--     | x `elem` nonPrincipal b    -> lookBox (x,dir) b `face` (y,dir')
--   VComN a b@(Box dir' y v nvs)
--     | x == y                     -> return u
--     | x `notElem` nonPrincipal b -> comM (fc a) (mapBoxM fc b)
--     | x `elem` nonPrincipal b    -> lookBox (x,dir) b `face` (y,dir')
--   VComp b@(Box dir' y _ _)
--     | x == y                     -> return u
--     | x `notElem` nonPrincipal b -> VComp <$> mapBoxM fc b
--     | x `elem` nonPrincipal b    -> lookBox (x,dir) b `face` (y,dir')
--   VFill z b@(Box dir' y v nvs)
--     | x == z                               -> return u
--     | x /= y && x `notElem` nonPrincipal b -> VFill z <$> mapBoxM fc b
--     | (x,dir) `elem` defBox b              ->
--       lookBox (x,dir) <$> mapBoxM (`face` (z,down)) b
--     | x == y && dir == dir'                ->
--         VComp <$> mapBoxM (`face` (z,up)) b
--   VInhRec b p h a     -> join $ inhrec <$> fc b <*> fc p <*> fc h <*> fc a
--   VApp u v            -> appM (fc u) (fc v)
--   VAppName u n        -> do
--    trace ("face " ++ "\nxdir " ++ show xdir ++
--           "\nu " ++ show u ++ "\nn " ++ show n)
--    appNameM (fc u) (faceName n xdir)
--   VSplit u v          -> appM (fc u) (fc v)
--   VVar s d            -> return $ VVar s [ faceName n xdir | n <- d ]
--   VFst p              -> fstSVal <$> fc p
--   VSnd p              -> sndSVal <$> fc p
--   VCircle             -> return VCircle
--   VBase               -> return VBase
--   VLoop y | x == y    -> return VBase
--           | otherwise -> return $ VLoop y
--   VCircleRec f b l s  -> join $ circlerec <$> fc f <*> fc b <*> fc l <*> fc s
--   VI  -> return VI
--   VI0 -> return VI0
--   VI1 -> return VI1
--   VLine y
--     | x == y && dir == down -> return VI0
--     | x == y && dir == up   -> return VI1
--     | otherwise             -> return $ VLine y
--   VIntRec f s e l u -> join $ intrec <$> fc f <*> fc s <*> fc e <*> fc l <*> fc u

conv :: Int -> Val -> Val -> Bool
conv k VU VU                                  = True
conv k (Ter (Lam x u) e) (Ter (Lam x' u') e') = do
  let v = mkVar k $ support (e, e')
  conv (k+1) (eval (Pair e (x,v)) u) (eval (Pair e' (x',v)) u')
conv k (Ter (Lam x u) e) u' = do
  let v = mkVar k $ support e
  conv (k+1) (eval (Pair e (x,v)) u) (app u' v)
conv k u' (Ter (Lam x u) e) = do
  let v = mkVar k $ support e
  conv (k+1) (app u' v) (eval (Pair e (x,v)) u)
conv k (Ter (Split p _) e) (Ter (Split p' _) e') =
  (p == p') && convEnv k e e'
conv k (Ter (Sum p _) e)   (Ter (Sum p' _) e') =
  (p == p') && convEnv k e e'
conv k (Ter (Undef p) e) (Ter (Undef p') e') =
  (p == p') && convEnv k e e'
conv k (VPi u v) (VPi u' v') = do
  let w = mkVar k $ support [u,u',v,v']
  conv k u u' && conv (k+1) (app v w) (app v' w)
conv k (VSigma u v) (VSigma u' v') = do
  let w = mkVar k $ support [u,u',v,v']
  conv k u u' && conv (k+1) (app v w) (app v' w)
conv k (VFst u) (VFst u')                     = conv k u u'
conv k (VSnd u) (VSnd u')                     = conv k u u'
conv k (VCon c us) (VCon c' us') =
  (c == c') && and (zipWith (conv k) us us')
conv k (VSPair u v)   (VSPair u' v')   = conv k u u' && conv k v v'
conv k (VSPair u v)   w                =
  conv k u (fstSVal w) && conv k v (sndSVal w)
conv k w              (VSPair u v)     =
  conv k (fstSVal w) u && conv k (sndSVal w) v
conv k (VApp u v)     (VApp u' v')     = conv k u u' && conv k v v'
conv k (VSplit u v)   (VSplit u' v')   = conv k u u' && conv k v v'
conv k (VVar x d)     (VVar x' d')     = (x == x') && (d == d')
conv k _              _                = False

convEnv :: Int -> Env -> Env -> Bool
convEnv k e e' = and $ zipWith (conv k) (valOfEnv e) (valOfEnv e')
