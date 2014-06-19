module Eval where

import Data.List
import Data.Maybe (fromMaybe)

import CTT

look :: Ident -> Env' -> (Binder, Val)
look x (k, e) = look' e
  where
    look' (Pair rho (n@(y,l),u))
      | x == y    = (n, u)
      | otherwise = look' rho
    look' r@(PDef es r1) = case lookupIdent x es of
      Just (y,t)  -> (y,eval (k,r) t)
      Nothing     -> look' r1

eval :: Env' -> Ter -> Val
eval (k,e) (U n)           = VU (n+k)
eval (k,e) (App r s)       = app (eval (k,e) r) (eval (k,e) s)
eval (k,e) (Var i)         = snd (look i (k,e))
eval (k,e) (Pi a b)        = VPi (eval (k,e) a) (eval (k,e) b)
eval (k,e) (Lam x t)       = Ter (Lam x t) (k,e) -- stop at lambdas
eval (k,e) (Sigma a b)     = VSigma (eval (k,e) a) (eval (k,e) b)
eval (k,e) (SPair a b)     = VSPair (eval (k,e) a) (eval (k,e) b)
eval (k,e) (Fst a)         = fstSVal (eval (k,e) a)
eval (k,e) (Snd a)         = sndSVal (eval (k,e) a)
eval (k,e) (Where t decls) = eval (k,PDef [ (x,y) | (x,_,y) <- decls ] e) t
eval (k,e) (Con name ts)   = VCon name (map (eval (k,e)) ts)
eval (k,e) (Split pr alts) = Ter (Split pr alts) (k,e)
eval (k,e) (Sum pr ntss)   = Ter (Sum pr ntss) (k,e)
eval (k,e) (Undef _)       = error "undefined"
eval (k,e) (Plus t)        = eval (k+1,e) t

vPlus :: Val -> Val
vPlus (VU n)         = VU (n+1)
vPlus (Ter t (k,e))  = Ter t (k+1, envPlus e)
vPlus (VPi u v)      = VPi (vPlus u) (vPlus v)
vPlus (VId u v w)    = VId (vPlus u) (vPlus v) (vPlus w)
vPlus (VSigma u v)   = VSigma (vPlus u) (vPlus v)
vPlus (VSPair u v)   = VSPair (vPlus u) (vPlus v)
vPlus (VCon name vs) = VCon name (map vPlus vs)
vPlus (VApp u v)     = VApp (vPlus u) (vPlus v)
vPlus (VSplit u v)   = VSplit (vPlus u) (vPlus v)
vPlus (VVar x)       = VVar x
vPlus (VFst u)       = VFst (vPlus u)
vPlus (VSnd u)       = VSnd (vPlus u)

envPlus :: Env -> Env
envPlus Empty             = Empty
envPlus (Pair e (x, u))   = Pair (envPlus e) (x, vPlus u)
envPlus (PDef bts e)      = PDef bts (envPlus e)

evals :: Env' -> [(Binder,Ter)] -> [(Binder,Val)]
evals (k,env) bts = [ (b,eval (k,env) t) | (b,t) <- bts ]

app :: Val -> Val -> Val
app (Ter (Lam x t) (k,e)) u = eval (k,Pair e (x,u)) t
app (Ter (Split _ nvs) (k,e)) (VCon name us) = case lookup name nvs of
    Just (xs,t) -> eval (upds (k,e) (zip xs us)) t
    Nothing -> error $ "app: Split with insufficient arguments; " ++
                        "missing case for " ++ name
app u@(Ter (Split _ _) _) v | isNeutral v = VSplit u v -- v should be neutral
                            | otherwise   = error $ "app: VSplit " ++ show v
                                                  ++ " is not neutral"
app r s | isNeutral r = VApp r s -- r should be neutral
        | otherwise   = error $ "app: VApp " ++ show r ++ " is not neutral"

fstSVal, sndSVal :: Val -> Val
fstSVal (VSPair a b)    = a
fstSVal u | isNeutral u = VFst u
          | otherwise   = error $ show u ++ " should be neutral"
sndSVal (VSPair a b)    = b
sndSVal u | isNeutral u = VSnd u
          | otherwise   = error $ show u ++ " should be neutral"

-- subtyping test
subt :: Int -> Val -> Val -> Bool
subt k (VU n) (VU m)                            = n <= m
subt k (Ter (Lam x u) (n,e)) (Ter (Lam x' u') (m,e')) = do
  let v = mkVar k
  subt (k+1) (eval (n,Pair e (x,v)) u) (eval (m,Pair e' (x',v)) u')
subt k (Ter (Lam x u) (n,e)) u' = do
  let v = mkVar k
  subt (k+1) (eval (n,Pair e (x,v)) u) (app u' v)
subt k u' (Ter (Lam x u) (n,e)) = do
  let v = mkVar k
  subt (k+1) (app u' v) (eval (n,Pair e (x,v)) u)
subt k (Ter (Split p _) (n,e)) (Ter (Split p' _) (m,e')) =
  (p == p') && subtEnv k e e' -- && (n <= m)
subt k (Ter (Sum p _) (n,e))   (Ter (Sum p' _) (m,e')) =
  (p == p') && subtEnv k e e' -- && (n <= m)
subt k (Ter (Undef p) (n,e)) (Ter (Undef p') (m,e')) =
  (p == p') && subtEnv k e e' -- && (n <= m)
subt k (VPi u v) (VPi u' v') = do
  let w = mkVar k
  subt k u' u && subt (k+1) (app v w) (app v' w)
subt k (VSigma u v) (VSigma u' v') = do
  let w = mkVar k
  subt k u u' && subt (k+1) (app v w) (app v' w)
subt k (VFst u) (VFst u') = subt k u u'
subt k (VSnd u) (VSnd u') = subt k u u'
subt k (VCon c us) (VCon c' us') =
  (c == c') && and (zipWith (subt k) us us')
subt k (VSPair u v) (VSPair u' v') = subt k u u' && subt k v v'
subt k (VSPair u v) w              =
  subt k u (fstSVal w) && subt k v (sndSVal w)
subt k w            (VSPair u v)   =
  subt k (fstSVal w) u && subt k (sndSVal w) v
subt k (VApp u v)   (VApp u' v')   = subt k u u' && subt k v v'
subt k (VSplit u v) (VSplit u' v') = subt k u u' && subt k v v'
subt k (VVar x)     (VVar x')      = x == x'
subt k _             _             = False

subtEnv :: Int -> Env -> Env -> Bool
subtEnv k e e' = and $ zipWith (subt k) (valOfEnv e) (valOfEnv e')
