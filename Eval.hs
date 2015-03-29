module Eval where

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
eval _ (Undef _)       = error "undefined"
eval e (CLam (i,_) t) = VCLam $ \j -> ceval i j $ eval e t
eval e (CApp r s) = capp (eval e r) s
eval e (CPair r s) = cpair (eval e r) (eval e s)
eval e (CPi a) = VCPi (eval e a)
eval e (Psi a) = VPsi (eval e a)
eval e (Param a) = VParam (eval e a)
eval e (Ni a b) = VNi (eval e a) (eval e b)

evals :: Env -> [(Binder,Ter)] -> [(Binder,Val)]
evals env bts = [ (b,eval env t) | (b,t) <- bts ]

cpair :: Val -> Val -> Val
cpair _ (VParam t) = t
cpair a b = VCPair a b

cevals :: [(Color,CVal)] -> Val -> Val
cevals [] = id
cevals ((i,j):xs) = ceval i j . cevals xs

substEnv :: Color -> CVal -> Env -> Env
substEnv i p env0 = case env0 of
  Empty -> Empty
  Pair env (b,v) -> Pair (re env) (b,ceval i p v)
  PDef ds env -> PDef (map (second $ subst i p) ds) (re env)
 where re = substEnv i p

second :: (t -> t2) -> (t1, t) -> (t1, t2)
second f (a,b) = (a, f b)

subst :: Color -> CVal -> Ter -> Ter
subst i p t0 =
  let su = subst i p
      subs = (\j -> if i==j then p else CVar j)
  in case t0 of
    App a b -> App (su a) (su b)
    Pi a b -> Pi (su a) (su b)
    Lam a b -> Lam a (su b)
    Sigma a b -> Sigma (su a) (su b)
    Fst b -> Fst (su b)
    Snd b -> Snd (su b)
    Where a ds -> Where (su a) [(b,su c, su d) | (b,c,d) <- ds]
    Var x -> Var x
    U -> U
    Con l ts -> Con l (map su ts)
    Split l bs -> Split l [(l',(bs',su t)) | (l',(bs',t)) <- bs]
    Sum b ss -> Sum b $ map (second (map (second su))) ss
    Undef l -> Undef l
    CLam (j,b) t | i /= j -> CLam (j,b) (su t)
                 | i == j -> CLam (i,b) (subst j p $ subst i (CVar j) t)
    CPair a b -> CPair (su a) (su b)
    CPi b -> CPi (su b)
    CApp a Zero -> CApp (su a) Zero
    CApp a (CVar k) -> CApp (su a) (subs k)
    Param a -> Param (su a)
    Psi a -> Psi (su a)
    Ni a b -> Ni (su a) (su b)

ceval :: Color -> CVal -> Val -> Val
ceval i p v0 =
  let ev = ceval i p
      subs = (\j -> if i==j then p else CVar j)
  in case v0 of
    VPi a b -> VPi (ev a) (ev b)
    VApp a b -> app (ev a) (ev b)
    VU -> VU
    Ter t env -> Ter (subst i p t) (substEnv i p env)
    VCPair a b -> cpair (ev a) (ev b)
    VCApp a Zero -> capp (ev a) Zero
    VCApp a (CVar k) -> capp (ev a) (subs k)
    VCPair a b -> cpair (ev a) (ev b)
    VCLam f -> clam' (ev . f)
    VCPi x -> VCPi (ev x)
    VPsi a -> VPsi (ev a)
    VNi a b -> ni (ev a) (ev b)
    VParam a -> param (ev a)

face v = v `capp` Zero

ni :: Val -> Val -> Val
ni (VCPair _ (VPsi p)) a = app p a
ni a b = VNi a b

param :: Val -> Val
param (VCPair _ p) = p
param x = VParam x

proj :: Color -> Val -> Val
proj i = ceval i Zero

clam' :: (CVal -> Val) -> Val
clam' f | (VCApp a (CVar "__RESERVED__")) <- f (CVar "__RESERVED__") = a
   -- eta contraction (no need for occurs check!)

clam :: Color -> Val -> Val
clam xi t = clam' (\i -> ceval xi i t)

capp :: Val -> CVal -> Val
capp (VCLam f) x = f x
capp (VCPair a _) Zero = a
capp f a = VCApp f a -- neutral

app :: Val -> Val -> Val
app (Ter (Lam x t) e) u = eval (Pair e (x,u)) t
app (Ter (Split _ nvs) e) (VCon name us) = case lookup name nvs of
    Just (xs,t) -> eval (upds e (zip xs us)) t
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

-- conversion test
conv :: Int -> Val -> Val -> Bool
conv k VU VU                                  = True
conv k (Ter (Lam x u) e) (Ter (Lam x' u') e') = do
  let v = mkVar k
  conv (k+1) (eval (Pair e (x,v)) u) (eval (Pair e' (x',v)) u')
conv k (Ter (Lam x u) e) u' = do
  let v = mkVar k
  conv (k+1) (eval (Pair e (x,v)) u) (app u' v)
conv k u' (Ter (Lam x u) e) = do
  let v = mkVar k
  conv (k+1) (app u' v) (eval (Pair e (x,v)) u)
conv k (Ter (Split p _) e) (Ter (Split p' _) e') =
  (p == p') && convEnv k e e'
conv k (Ter (Sum p _) e)   (Ter (Sum p' _) e') =
  (p == p') && convEnv k e e'
conv k (Ter (Undef p) e) (Ter (Undef p') e') =
  (p == p') && convEnv k e e'
conv k (VPi u v) (VPi u' v') = do
  let w = mkVar k
  conv k u u' && conv (k+1) (app v w) (app v' w)
conv k (VSigma u v) (VSigma u' v') = do
  let w = mkVar k
  conv k u u' && conv (k+1) (app v w) (app v' w)
conv k (VFst u) (VFst u') = conv k u u'
conv k (VSnd u) (VSnd u') = conv k u u'
conv k (VCon c us) (VCon c' us') =
  (c == c') && and (zipWith (conv k) us us')
conv k (VSPair u v) (VSPair u' v') = conv k u u' && conv k v v'
conv k (VSPair u v) w              =
  conv k u (fstSVal w) && conv k v (sndSVal w)
conv k w            (VSPair u v)   =
  conv k (fstSVal w) u && conv k (sndSVal w) v
conv k (VApp u v)   (VApp u' v')   = conv k u u' && conv k v v'
conv k (VSplit u v) (VSplit u' v') = conv k u u' && conv k v v'
conv k (VVar x)     (VVar x')      = x == x'
conv k _              _            = False

convEnv :: Int -> Env -> Env -> Bool
convEnv k e e' = and $ zipWith (conv k) (valOfEnv e) (valOfEnv e')
