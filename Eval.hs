{-# LANGUAGE PatternSynonyms #-}
module Eval where

import CTT
import Control.Applicative
import Data.Monoid hiding (Sum)

look :: Ident -> Env -> (Binder, Val)
look x (Pair rho (n@(y,l),u))
  | x == y    = (n, u)
  | otherwise = look x rho
look x r@(PDef es r1) = case lookupIdent x es of
  Just (y,t)  -> (y,eval r t)
  Nothing     -> look x r1
look x (PCol rho _) = look x rho

lkCol :: Ident -> Env -> (Binder, CVal)
lkCol i (Pair e _) = lkCol i e
lkCol i (PDef _ e) = lkCol i e
lkCol i (PCol e (n@(j,_),v)) | i == j = (n,v)
                             | otherwise = lkCol i e
lkCol i Empty = error $ "Color " ++ show i ++ " not found"


reAbsEnvOnCol :: Ident -> CVal -> Env -> Env
reAbsEnvOnCol x _ Empty = Empty
reAbsEnvOnCol x i (Pair e (b,v)) = Pair (reAbsEnvOnCol x i e) (b, reabs)
  where reabs = case i of
          CVar j -> clam j v
          Zero -> clam' $ \_ -> v
reAbsEnvOnCol x i (PCol e ((x',_), c)) | x == x' = e
reAbsEnvOnCol x i (PCol e c) = PCol (reAbsEnvOnCol x i e) c
reAbsEnvOnCol x i (PDef xas e) = PDef xas (reAbsEnvOnCol x i e) -- ???

reAbsWholeEnvOnCol :: CTer -> Env -> Env
reAbsWholeEnvOnCol Zero e = e
reAbsWholeEnvOnCol (CVar i) e = reAbsEnvOnCol i (colEval e (CVar i)) e


eval :: Env -> Ter -> Val
eval e U               = VU
eval e (CU cs)         = VV . Just $ concat $ map (\c -> catMax (colEval e (CVar c))) cs
eval e (App r s)       = sh2 app (eval e r) (eval e s)
eval e (Var i)         = snd (look i e)
eval e (Pi a b)        = VPi (eval e a) (eval e b)
-- eval e (Lam is x t)    = Ter (Lam is x t) e -- stop at lambdas
eval e (Lam x t)       = VLam $ \x' -> eval (Pair e (x,x')) t
eval e (Sigma a b)     = VSigma (eval e a) (eval e b)
eval e (SPair a b)     = VSPair (eval e a) (eval e b)
eval e (Fst a)         = sh1 fstSVal (eval e a)
eval e (Snd a)         = sh1 sndSVal (eval e a)
eval e (Where t decls) = eval (PDef [ (x,y) | (x,_,y) <- decls ] e) t
eval e (Con name ts)   = VCon name (map (eval e) ts)
eval e (Split pr alts) = Ter (Split pr alts) e
eval e (Sum pr ntss)   = Ter (Sum pr ntss) e
eval _ (Undef _)       = error "undefined (2)"
eval e (CLam x t) = clam' $ \i' -> eval (PCol e (x,i')) t
eval e (CApp r s) = sh2' capp (eval e' r) (colEval e s)
  where e' = reAbsWholeEnvOnCol s e
eval e (CPair r s) = sh2 cpair (eval e r) (eval e s)
eval e (CPi a) = VCPi (eval e a)
eval e (Psi _ a) = sh1 psi (eval e a)
eval e (Phi a b) = VPhi (eval e a) (eval e b)
eval e (Param a) = sh1 param (eval e a)
eval e (Ni a b) = sh2 ni (eval e a) (eval e b)
eval e (Rename c t) = case colEval e c of
                        Zero   -> clam' $ \_ ->             (eval e t)
                        CVar i -> clam' $ \i' -> ceval i i' (eval e t)

vconstr Infty = id
vconstr c = VConstr c

colEval :: Env -> CTer -> CVal
colEval _ Zero = Zero
colEval e (Max i j) = maxx (colEval e i) (colEval e j)
colEval e (CVar i) = snd $ lkCol i e

psi :: Val -> Val
psi (VLam f)
  | VNi a (VVar "__RESERVED__") <- f $ VVar "__RESERVED__"
  -- FIXME: occurs check!
  = param a 
psi a = VPsi a

evals :: Env -> [(Binder,Ter)] -> [(Binder,Val)]
evals env bts = [ (b,eval env t) | (b,t) <- bts ]

cpair :: Val -> Val -> Val
cpair _ (VParam t) = t
cpair (VV (Just xs)) VU = clam' $ \i -> VV (Just (catMax i ++ xs))
-- cpair a b | fizzle a = clam' $ \i -> vconstr i b
cpair a b = VCPair a b

cevals :: [(Color,CVal)] -> Val -> Val
cevals [] = id
cevals ((i,j):xs) = ceval i j . cevals xs

-- substEnv :: Color -> CVal -> Env -> Env
-- substEnv i p env0 = case env0 of
--   Empty -> Empty
--   Pair env (b,v) -> Pair (re env) (b,ceval i p v)
--   PDef ds env -> PDef (map (second $ subst i p) ds) (re env)
--  where re = substEnv i p

second :: (t -> t2) -> (t1, t) -> (t1, t2)
second f (a,b) = (a, f b)
                 
-- subst :: Color -> CVal -> Ter -> Ter
-- subst i p t0 =
--   let su = subst i p
--       subs = (\j -> if i==j then p else CVar j)
--   in case t0 of
--     App a b -> App (su a) (su b)
--     Pi a b -> Pi (su a) (su b)
--     Lam is _ _ | Zero <- p, not (null is) -> error $ "should be gone: " ++ show t0
--     Lam is x b -> Lam [j | CVar j <- map subs is] x (su b)
--     Sigma a b -> Sigma (su a) (su b)
--     Fst b -> Fst (su b)
--     Snd b -> Snd (su b)
--     Where a ds -> Where (su a) [(b,su c, su d) | (b,c,d) <- ds]
--     Var x -> Var x
--     U -> U
--     Con l ts -> Con l (map su ts)
--     Split l bs -> Split l [(l',(bs',su t)) | (l',(bs',t)) <- bs]
--     Sum b ss -> Sum b $ map (second (map (second su))) ss
--     Undef l -> Undef l
--     CLam (j,b) t | CVar k <- p, k == j -> error "nope"
--                  | i == j -> t0
--                  | otherwise -> CLam (j,b) (su t)
--     CPair a b -> CPair (su a) (su b)
--     CPi b -> CPi (su b)
--     CApp a Zero -> CApp (su a) Zero
--     CApp a (CVar k) -> CApp (su a) (subs k)
--     Param a -> Param (su a)
--     Psi a -> Psi (su a)
--     Ni a b -> Ni (su a) (su b)

cevalEnv :: Color -> CVal -> Env -> Env
cevalEnv i p (Pair e (b,v)) = cevalEnv i p e `Pair` (b, ceval i p v)
cevalEnv i p (PDef d e) = PDef d $ cevalEnv i p e
cevalEnv i p (PCol e (b,p')) = PCol (cevalEnv i p e) (b, cceval i p p')
cevalEnv i p Empty = Empty

cceval :: Color -> CVal -> CVal -> CVal
cceval i p (CVar k) | k == i = p
cceval i p (Max x y) = maxx (cceval i p x) (cceval i p y)
cceval _ _ a = a

catMax :: CVal -> [Color]
catMax (CVar x) = [x]
catMax (Max x y) = catMax x ++ catMax y
catMax Zero = []

ceval :: Color -> CVal -> Val -> Val
ceval i p v0 =
  let ev = ceval i p
  in case v0 of
    VV x -> VV $ fmap (concatMap (catMax . cceval i p . CVar)) x 
    Ter t env -> Ter t (cevalEnv i p env)
    VPi a b -> VPi (ev a) (ev b)
    VSigma a b -> VSigma (ev a) (ev b)
    VSPair a b -> VSPair (ev a) (ev b)
    VCon x as -> VCon x (map ev as)
    VApp a b -> app (ev a) (ev b)
    VSplit a b -> VSplit (ev a) (ev b)
    VVar x -> VVar x
    VFst a -> VFst (ev a)
    VSnd a -> VSnd (ev a)
    VCApp a b ->  capp (ev a) (cceval i p b)
    VCPi x -> VCPi (ev x)
    VCLam f -> VCLam $ \j -> ev (f j)
--    VCLam j a | i == j -> v0
--              | otherwise -> VCLam k (ev $ ceval j (CVar k) a)
--         where k = Color $ fresh (a,p)
    VCPair a b -> cpair (ev a) (ev b)
    VParam a -> param (ev a)
    VPsi a -> psi (ev a)
    VNi a b -> ni (ev a) (ev b)
    VLam f -> VLam (ev . f)
    VConstr c a -> vconstr (cceval i p c) (ev a)
    VFizzle -> VFizzle

face :: Val -> Val
face v = v `capp` Zero

ni :: Val -> Val -> Val
ni (VCPair VFizzle a) _ = a
ni (VCPair (VV (Just [])) a) _ = a
ni (VCLam f) _ | (VV (Just [i'])) <- f $ CVar $ i,  i == i' = VU
  where i = Color "__NI__UNIV__"
ni (VCPair _ (VPsi p)) a = app p a
-- ni a _ | Just a' <- fizz a = a'
ni a b = VNi a b

sh1 :: (Val -> Val) -> Val -> Val
sh1 f (VConstr c a) = vconstr c (sh1 f a)
sh1 f a = f a

sh2 :: (Val -> Val -> Val) -> Val -> Val -> Val
sh2 f (VConstr c a) b = vconstr c (sh2 f a b)
sh2 f a (VConstr c b) = vconstr c (sh2 f a b)
sh2 f a b = f a b

sh2' :: (Val -> a -> Val) -> Val -> a -> Val
sh2' f (VConstr c a) b = vconstr c (sh2' f a b)
sh2' f a b = f a b

param :: Val -> Val
param (VCPair _ p) = p
-- param x | Just x' <- fizz x = x'
param x = VParam x

proj :: Color -> Val -> Val
proj i = ceval i Zero

clam' :: (CVal -> Val) -> Val
clam' = VCLam

  --       f = clam k (f $ CVar k)
  -- where k = Color $ fresh (f $ CVar $ Color "__CLAM'__")
  --           -- FIXME: this is not good, because the fresh variable may
  --           -- capture some variables present in types.

clam :: Color -> Val -> Val
-- clam i (VCApp a (CVar i')) | i == i' = a   -- eta contraction (no need for occurs check!)
clam i a = VCLam $ \i' -> ceval i i' a

clams :: [Color] -> Val -> Val
clams [] t = t
clams (i:is) t = clam i $ clams is t

cpis :: [Color] -> Val -> Val
cpis [] t = t
cpis (i:is) t = VCPi $ clam i $ cpis is t

cpi :: Color -> Val -> Val
cpi i t = VCPi $ clam i t

capp :: Val -> CVal -> Val
capp (VCLam f) x = f x
capp (VCPair a _) Zero = a
-- capp (VCPair _ (VPsi p)) Infty = p `app` VVar "__CAPP_INFTY__"
capp (VPhi f _) Zero = f
capp f a = VCApp f a -- neutral

capps :: Val -> [Color] -> Val
capps a [] = a
capps a (i:is) = capps (capp a $ CVar i) is

app :: Val -> Val -> Val
app (VCApp (VPhi f g) (CVar i)) u = VCPair (f `app` proj i u) (g `app` clam i u) `capp` CVar i
-- <f,g>@i u = [f u(i0), g <i>u]@i
app (VLam f) u = f u
-- app (Ter (Lam cs x t) e) u = eval (Pair e (x,clams cs u)) t
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
fstSVal (VSPair a _)    = a
fstSVal u | isNeutral u = VFst u
          | otherwise   = error $ show u ++ " should be neutral"
sndSVal (VSPair _ b)    = b
sndSVal u | isNeutral u = VSnd u
          | otherwise   = error $ show u ++ " should be neutral"

equal :: (Show a, Eq a) => a -> a -> Maybe [Char]
equal a b | a == b = Nothing
          | otherwise = different a b
different a b = Just $ show a ++ " /= " ++ show b
-- conversion test
conv :: Int -> Val -> Val -> Maybe String
conv k (VConstr _ x) y = conv k x y
conv k y (VConstr _ x) = conv k x y
conv k (VLam f) t = conv (k+1) (f v) (t `app` v)
  where v = mkVar k
conv k t (VLam f) = conv (k+1) (f v) (t `app` v)
  where v = mkVar k
conv k (VCPi f) (VCPi f') = conv k f f'
conv k (VCLam f) t = conv (k+1) (f c) (capp t c)
  where c = mkCol k
conv k t (VCLam f) = conv k (VCLam f) t
conv k (VCApp a b) (VCApp a' b') = conv k a a' <> equal b b'
conv k (VParam a) (VParam a') = conv k a a'
conv k (VParam a) b = conv k a (VCPair (face a) b)
conv k b (VParam a) = conv k a (VCPair (face a) b)
conv k (VPsi a) (VPsi a') = conv k a a'
conv k (VNi a b) (VNi a' b') = conv k a a' <> conv k b b'
conv k (VCPair a b) (VCPair a' b') = conv k a a' <> conv k b b'
conv k (VPhi a b) (VPhi a' b') = conv k a a' <> conv k b b'
conv k (VPhi f g) fp@(VCPair f' _) = conv k f f' <> conv (k+1) (g `app` x) (VParam $ clam' $ \i -> (fp `capp` i) `app` (x `capp` i))
  where x = mkVar k
conv k fg@(VPhi _ _) fp@(VCPair _ _) = conv k fp fg
conv _ (VV x) (VV y)                                  = equal x y
conv _ VFizzle _                                  = Nothing
conv _ _  VFizzle                                 = Nothing
-- conv k (Ter (Lam cs x u) e) (Ter (Lam cs' x' u') e') = do
--   let v = mkVar k
--   cs `equal` cs' <> conv (k+1) (eval (Pair e (x,v)) u) (eval (Pair e' (x',v)) u')
-- conv k (Ter (Lam is x u) e) u' = do
--   let v = mkVar k
--   conv (k+1) (eval (Pair e (x,clams is v)) u) (app u' v)
-- conv k u' (Ter (Lam is x u) e) = do
--   let v = mkVar k
--   conv (k+1) (app u' v) (eval (Pair e (x,clams is v)) u)
conv k (Ter (Split p _) e) (Ter (Split p' _) e') =
  (p `equal` p') <> convEnv k e e'
conv k (Ter (Sum p _) e)   (Ter (Sum p' _) e') =
  (p `equal` p') <> convEnv k e e'
conv k (Ter (Undef p) e) (Ter (Undef p') e') =
  (p `equal` p') <> convEnv k e e'
conv k (VPi u v) (VPi u' v') = do
  let w = mkVar k
  conv k u u' <> conv (k+1) (app v w) (app v' w)
conv k (VSigma u v) (VSigma u' v') = do
  let w = mkVar k
  conv k u u' <> conv (k+1) (app v w) (app v' w)
conv k (VFst u) (VFst u') = conv k u u'
conv k (VSnd u) (VSnd u') = conv k u u'
conv k (VCon c us) (VCon c' us') =
  (c `equal` c') <> mconcat (zipWith (conv k) us us')
conv k (VSPair u v) (VSPair u' v') = conv k u u' <> conv k v v'
conv k (VSPair u v) w              =
  conv k u (fstSVal w) <> conv k v (sndSVal w)
conv k w            (VSPair u v)   =
  conv k (fstSVal w) u <> conv k (sndSVal w) v
conv k (VApp u v)   (VApp u' v')   = conv k u u' <> conv k v v'
conv k (VSplit u v) (VSplit u' v') = conv k u u' <> conv k v v'
conv _ (VVar x)     (VVar x')      = x `equal` x'
conv _ x              x'           = different x x'

convEnv :: Int -> Env -> Env -> Maybe String
convEnv k e e' = mconcat $ zipWith (conv k) (valOfEnv e) (valOfEnv e')

