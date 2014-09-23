{-# LANGUAGE CPP #-}
module Eval ( eval
            , evals
            , app
            , conv
            , fstSVal
            ) where

import Control.Arrow (second)
import Data.List
import Data.Maybe (fromMaybe)
import qualified Debug.Trace as DT
import Connections
import Pretty

import Data.Map (Map,(!))
import Data.Set (Set)
import qualified Data.Map as Map
import qualified Data.Set as Set

import CTT

debug :: Bool
#ifdef debugmode
debug = True
#else
debug = False
#endif

trace :: String -> a -> a
trace s e = if debug then DT.trace s e else e

look :: Ident -> Env -> (Binder, Val)
look x (Pair rho (n@(y,l),u))
  | x == y    = (n, u)
  | otherwise = look x rho
look x r@(PDef es r1) = case lookupIdent x es of
  Just (y,t)  -> (y,eval r t)
  Nothing     -> look x r1

eval :: Env -> Ter -> Val
eval e U                 = VU
eval e (PN pn)           = evalAppPN e pn []
eval e t@(App r s)       = case unApps t of
  (PN pn,us) -> evalAppPN e pn us
  _          -> app (eval e r) (eval e s)
eval e (Var i)           = snd $ look i e
eval e (Pi a b)          = VPi (eval e a) (eval e b)
eval e (Lam x t)         = Ter (Lam x t) e -- stop at lambdas
eval e (Where t decls)   = eval (PDef (declDefs decls) e) t

eval e (Sigma a b)       = VSigma (eval e a) (eval e b)
eval e (SPair a b)       = VSPair (eval e a) (eval e b)
eval e (Fst a)           = fstSVal $ eval e a
eval e (Snd a)           = sndSVal $ eval e a

eval e (Sum pr ntss)     = Ter (Sum pr ntss) e
eval e (Con name ts)     = VCon name $ map (eval e) ts
eval e (Split pr alts)   = Ter (Split pr alts) e


evals :: Env -> [(Binder,Ter)] -> [(Binder,Val)]
evals env = map (second (eval env))

fstSVal, sndSVal :: Val -> Val
fstSVal (VSPair a b)    = a
fstSVal u | isNeutral u = VFst u
          | otherwise   = error $ show u ++ " should be neutral"
sndSVal (VSPair a b)    = b
sndSVal u | isNeutral u = VSnd u
          | otherwise   = error $ show u ++ " should be neutral"

instance Nominal Val where
  support VU                            = []
  support (Ter _ e)                     = support e
  support (VPi v1 v2)                   = support [v1,v2]
  support (Kan i a ts u)                = i `delete` support (a,ts,u)
  support (KanUElem ts u)               = support (ts,u)
  support (UnKan ts u)                  = support (ts, u)

  support (VId a v0 v1)                 = support [a,v0,v1]
  support (Path i v)                    = i `delete` support v

  support (VSigma u v)                  = support (u,v)
  support (VSPair u v)                  = support (u,v)
  support (VFst u)                      = support u
  support (VSnd u)                      = support u

  support (VCon _ vs)                   = support vs

  support (VVar _ phis)                 = support phis
  support (VApp u v)                    = support (u, v)
  support (VAppFormula u phi)           = support (u, phi)
  support (VSplit u v)                  = support (u, v)

  support (Glue ts u)                   = support (ts, u)
  support (UnGlue ts u)                 = support (ts, u)
  support (GlueElem ts u)               = support (ts, u)
  support (HisoProj _ e)                = support e

  support (VExt phi f g p)              = support (phi,f,g,p)

  -- support (VInh v)                      = support v
  -- support (VInc v)                      = support v
  -- support (VSquash x v0 v1)             = support (x, [v0,v1])
  -- -- support (VExt x b f g p)           = support (x, [b,f,g,p])
  -- support (VHExt x b f g p)             = support (x, [b,f,g,p])
  -- support (Kan Fill a box)              = support (a, box)
  -- support (VFillN a box)                = support (a, box)
  -- support (VComN   a box@(Box _ n _ _)) = delete n (support (a, box))
  -- support (Kan Com a box@(Box _ n _ _)) = delete n (support (a, box))
  -- support (VEquivEq x a b f s t)        = support (x, [a,b,f,s,t])
  --          -- names x, y and values a, s, t
  -- support (VEquivSquare x y a s t)      = support ((x,y), [a,s,t])
  -- support (VPair x a v)                 = support (x, [a,v])
  -- support (VComp box@(Box _ n _ _))     = delete n $ support box
  -- support (VFill x box)                 = delete x $ support box
  -- support (VInhRec b p h a)             = support [b,p,h,a]
  -- support VCircle                       = []
  -- support VBase                         = []
  -- support (VLoop n)                     = [n]
  -- support (VCircleRec f b l s)          = support [f,b,l,s]
  -- support VI                            = []
  -- support VI0                           = []
  -- support VI1                           = []
  -- support (VLine n)                     = [n]
  -- support (VIntRec f s e l u)           = support [f,s,e,l,u]
  -- support v                             = error ("support " ++ show v)


  act u (i, phi) = -- trace ("act" <+> show u <+> parens (show i <+> "=" <+> show phi)) $
    let acti :: Nominal a => a -> a
        acti u = act u (i, phi)
    in case u of
         VU      -> VU
         Ter t e -> Ter t (acti e)
         VPi a f -> VPi (acti a) (acti f)
         Kan j a ts u -> comp Pos k (ar a) (ar ts) (ar u)
              where k   = fresh (u, Atom i, phi)
                    ar :: Nominal a => a -> a
                    ar = acti . (`rename` (j,k))

         KanUElem ts u -> kanUElem (acti ts) (acti u)
         UnKan ts u    -> UnKan (acti ts) (acti u)

         VId a u v -> VId (acti a) (acti u) (acti v)
         Path j v -> Path k (acti (v `rename` (j,k)))
              where k = fresh (v, Atom i, phi)

         VSigma a f -> VSigma (acti a) (acti f)
         VSPair u v -> VSPair (acti u) (acti v)
         VFst u     -> VFst (acti u)
         VSnd u     -> VSnd (acti u)

         VCon c vs  -> VCon c (acti vs)

         VVar x psis       -> VVar x (acti psis)
         VAppFormula u psi -> acti u @@ acti psi
         VApp u v          -> app (acti u) (acti v)
         VSplit u v        -> app (acti u) (acti v)

         Glue ts u         -> glue (acti ts) (acti u)
         UnGlue ts u       -> UnGlue (acti ts) (acti u)
         GlueElem ts u     -> glueElem (acti ts) (acti u)
         HisoProj n e      -> HisoProj n (acti e)

         VExt psi f g p -> vext (acti psi) (acti f) (acti g) (acti p)

instance Nominal Hiso where
  support (Hiso a b f g s t)  = support (a,b,f,g,s,t)
  act (Hiso a b f g s t) iphi = Hiso a' b' f' g' s' t'
    where (a', b', f', g', s', t') = act (a,b,f,g,s,t) iphi

instance Nominal Env where
  act e iphi = mapEnv (\u -> act u iphi) e

  support Empty          = []
  support (Pair e (_,v)) = support (e, v)
  support (PDef _ e)     = support e

-- Glueing
glue :: System Hiso -> Val -> Val
glue hisos b | Map.null hisos         = b
glue hisos b | eps `Map.member` hisos = hisoA (hisos ! eps)
glue hisos b = Glue hisos b

glueElem :: System Val -> Val -> Val
glueElem us v | Map.null us         = v
glueElem us v | eps `Map.member` us = us ! eps
glueElem us v = GlueElem us v

kanUElem :: System Val -> Val -> Val
kanUElem us v | Map.null us         = v
kanUElem us v | eps `Map.member` us = us ! eps
kanUElem us (KanUElem vs w) = KanUElem ws w
  where
    ws' = Map.mapWithKey (\alpha vAlpha -> kanUElem (us `face` alpha) vAlpha) vs
    ws  = insertsSystem (Map.toList us) ws'
kanUElem us v = KanUElem us v

vext :: Formula -> Val -> Val -> Val -> Val
vext (Dir Zero) f _ _ = f
vext (Dir One)  _ g _ = g
vext phi f g p        = VExt phi f g p


-- Application
app :: Val -> Val -> Val
app (Ter (Lam x t) e) u            = eval (Pair e (x,u)) t
app kan@(Kan i b@(VPi a f) ts li0) ui1 = trace "app (Kan VPi)" $
    let j   = fresh (Atom i,kan,ui1)
        (aj,fj,tsj) = (a,f,ts) `rename` (i,j)
        u   = fill Neg j aj Map.empty ui1
        ui0 = act u (j, Dir 0)
    in comp Pos j (app fj u)
           (Map.intersectionWith app tsj (border u tsj))
           (app li0 ui0)
app (Ter (Split _ nvs) e) (VCon name us) = case lookup name nvs of
    Just (xs,t)  -> eval (upds e (zip xs us)) t
    Nothing -> error $ "app: Split with insufficient arguments; " ++
                        "missing case for " ++ name

app g@(UnGlue hisos b) w
    | Map.null hisos         = w
    | eps `Map.member` hisos = app (hisoF (hisos ! eps)) w
    | otherwise              = case w of
       GlueElem us v -> v
       _             -> VApp g w

app g@(UnKan hisos b) w
    | Map.null hisos         = w
    | eps `Map.member` hisos = app (hisoF (hisos ! eps)) w
    | otherwise              = case w of
       KanUElem us v -> v
       _             -> VApp g w

-- TODO: recheck at least 2 more times (please decrease the counter if
-- you checked)
app (HisoProj hisoProj e) u = case hisoProj of
    HisoSign sign -> comp sign i (e @@ i) Map.empty u
    -- f (g y) -> y
    IsSection     ->
      let ts = Map.fromList [(i ~> 0, line Pos j (appiso Neg u)), (i ~> 1, u)]
      in  Path i $ comp Pos j (e @@ (Atom i :\/: Atom j)) ts (line Neg i u)
    -- g (f x) -> x
    IsRetraction ->
      let ts = Map.fromList [(i ~> 0, u), (i ~> 1, line Neg j (appiso Pos u))]
      in Path i $ (comp Neg j (e @@ (Atom i :/\: Atom j)) ts (line Pos i u)) `sym` i
  where i:j:_ = freshs (e, u)
        appiso sign v = app (HisoProj (HisoSign sign) e) v
        line sign k v = fill sign k (e @@ k) Map.empty v

app u@(Ter (Split _ _) _) v
  | isNeutral v = VSplit u v -- v should be neutral
  | otherwise   = error $ "app: (VSplit) " ++ show v ++ " is not neutral"
app u@(VExt phi f g p) v = (app p v) @@ phi
app r s
  | isNeutral r = VApp r s -- r should be neutral
  | otherwise   = error $ "app: (VApp) " ++ show r ++ " is not neutral"

-- app vext@(VExt x bv fv gv pv) w = do
--   -- NB: there are various choices how to construct this
--   let y = fresh (vext, w)
--   w0    <- w `face` (x,down)
--   left  <- app fv w0
--   right <- app gv (swap w x y)
--   pvxw  <- appFormulaM (app pv w0) x
--   comM (app bv w) (return (Box up y pvxw [((x,down),left),((x,up),right)]))
-- app vhext@(VHExt x bv fv gv pv) w =
--   let a0 = w `face` (x,down)
--       a1 = w `face` (x,up)
--   in appFormula (apps pv [a0, a1, Path x w]) x
-- app r s
--   | isNeutral r = VApp r s -- r should be neutral
--   | otherwise   = error $ "app: (VApp) " ++ show r ++ " is not neutral"

apps :: Val -> [Val] -> Val
apps = foldl app

(@@) :: ToFormula a => Val -> a -> Val
(Path i u) @@ phi = u `act` (i, toFormula phi)
v @@ phi          = VAppFormula v (toFormula phi)

-- where j = fresh (u, Atom i, phi)
-- | y `elem` [0,1] = u `face` (x,y)
-- appFormula p y          | y `elem` [0,1] = VAppFormula p y -- p has to be neutral
-- appFormula (Path x u) y | x == y             = u
--                      | y `elem` support u = error ("appFormula " ++ "\nu = " ++
--                                                    show u ++ "\ny = " ++ show y)
--                      | otherwise          = swap u x y
-- appFormula v y          = VAppFormula v y

-- Grad Lemma, takes a iso an L-system ts a value v s.t. sigma us = border v
-- outputs u s.t. border u = us and an L-path between v and sigma u
-- an theta is a L path if L-border theta is constant
gradLemma :: Hiso -> System Val -> Val -> (Val, Val)
gradLemma hiso@(Hiso a b f g s t) us v = (u, Path i theta'')
  where i:j:_   = freshs (hiso, us, v)
        us'     = Map.mapWithKey (\alpha uAlpha -> app (t `face` alpha) uAlpha @@ i) us
        theta   = fill Pos i a us' (app g v)
        u       = theta `face` (i ~> 1)
        ws      = insertSystem (i ~> 0) (app g v) $
                  insertSystem (i ~> 1) (app t u @@ j) $
                  Map.mapWithKey (\alpha uAlpha -> app (t `face` alpha) uAlpha @@ (Atom i :/\: Atom j)) us
        theta'  = comp Neg j a ws theta
        xs      = insertSystem (i ~> 0) (app s v @@ j) $
                  insertSystem (i ~> 1) (app s (app f u) @@ j) $
                  Map.mapWithKey (\alpha uAlpha -> app (s `face` alpha) (app (f `face` alpha) uAlpha) @@ j) us
        theta'' = comp Pos j b xs (app f theta')

eqHiso :: Val -> Hiso
eqHiso e = Hiso (e @@ Zero) (e @@ One)
                (HisoProj (HisoSign Pos) e) (HisoProj (HisoSign Neg) e)
                (HisoProj IsSection e) (HisoProj IsRetraction e)

-- Apply a primitive notion
evalAppPN :: Env -> PN -> [Ter] -> Val
evalAppPN e pn ts
  | length ts < arity pn =
      -- Eta expand primitive notions
      let r       = arity pn - length ts
          binders = map (\n -> '_' : show n) [1..r]
          vars    = map Var binders
      in Ter (mkLams binders $ mkApps (PN pn) (ts ++ vars)) e
  | otherwise =
      let (args,rest) = splitAt (arity pn) ts
          vas = map (eval e) args
          p   = evalPN (freshs e) pn vas
          r   = map (eval e) rest
      in apps p r

-- Evaluate primitive notions
evalPN :: [Name] -> PN -> [Val] -> Val
evalPN (i:_) Id            [a,a0,a1]     = VId (Path i a) a0 a1
evalPN (i:_) IdP           [_,_,p,a0,a1] = VId p a0 a1
evalPN (i:_) Refl          [_,a]         = Path i a
evalPN (i:_) TransU        [_,_,p,t]     = trace "evalPN TransU" $ comp Pos i (p @@ i) Map.empty t
evalPN (i:_) TransInvU     [_,_,p,t]     = comp Neg i (p @@ i) Map.empty t
-- figure out how to turn TransURef into a definitional equality (pb for neutral terms)
evalPN (i:_) TransURef     [a,t]         = Path i $ fill Pos i a Map.empty t
-- evalPN (x:_) TransUEquivEq [_,b,f,_,_,u] =
--   Path x $ fill b (Box up x (app f u) [])   -- TODO: Check this!
evalPN (i:j:_) CSingl [_,_,_,p] = Path i $ VSPair q (Path j (q `connect` (i,j)))
  where q = p @@ i
evalPN (i:_) Ext [_,_,f,g,p] = Path i $ VExt (Atom i) f g p
-- evalPN (x:_)   HExt       [_,b,f,g,p]   = Path x $ VHExt x b f g p
-- evalPN _       Inh        [a]           = VInh a
-- evalPN _       Inc        [_,t]         = VInc t
-- evalPN (x:_)   Squash     [_,r,s]       = Path x $ VSquash x r s
-- evalPN _       InhRec     [_,b,p,phi,a] = inhrec b p phi a
-- evalPN (x:_)   EquivEq    [a,b,f,s,t]   = Path x $ VEquivEq x a b f s t
evalPN (i:_)   HisoEq    [a,b,f,g,s,t]   =
  Path i $ Glue (mkSystem [(i ~> 0, Hiso a b f g s t)]) b
-- evalPN (x:y:_) EquivEqRef [a,s,t]       =
--   Path y $ Path x $ VEquivSquare x y a s t
evalPN (i:_)   MapOnPath  [_,_,f,_,_,p]    = Path i $ app f (p @@ i)
evalPN (i:_)   MapOnPathD [_,_,f,_,_,p]    = Path i $ app f (p @@ i)
evalPN (i:_)   AppOnPath [_,_,_,_,_,_,p,q] = Path i $ app (p @@ i) (q @@ i)
evalPN (i:_)   MapOnPathS [_,_,_,f,_,_,p,_,_,q] =
  Path i $ app (app f (p @@ i)) (q @@ i)
-- evalPN _       Circle     []               = VCircle
-- evalPN _       Base       []               = VBase
-- evalPN (x:_)   Loop       []               = Path x $ VLoop x
-- evalPN _       CircleRec  [f,b,l,s]        = circlerec f b l s
-- evalPN _       I          []               = VI
-- evalPN _       I0         []               = VI0
-- evalPN _       I1         []               = VI1
-- evalPN (x:_)   Line       []               = Path x $ VLine x
-- evalPN _       IntRec     [f,s,e,l,u]      = intrec f s e l u
evalPN _       u          _                = error ("evalPN " ++ show u)

-- appS1 :: Val -> Val -> Name -> Eval Val
-- appS1 f p x | x `elem` [0,1] = appFormula p x
-- appS1 f p x = do
--   let y = fresh (p,(f,x))
--   q <- appFormula p y
--   a <- appFormula p 0
--   b <- appFormula p 1
--   newBox <- Box down y b <$>
--             sequenceSnd  [ ((x,down),q `face` (x,down))
--                          , ((x,up),b `face` (x,up))]
--   fb <- app f VBase
--   fl <- app f (VLoop y)
--   tu <- fillM (return VU) (Box down y fb <$>
--                            sequenceSnd [ ((x,down),fl `face` (x,down))
--                                        , ((x,up),fb `face` (x,up))])
--   com tu newBox

-- Compute the face of an environment
faceEnv :: Env -> Face -> Env
faceEnv e alpha = mapEnv (`face` alpha) e


-- isNeutralFill :: Val -> Box Val -> Bool
-- isNeutralFill v box | isNeutral v               = True
-- isNeutralFill v@(Ter (PN (Undef _)) _) box      = True
-- isNeutralFill (Ter (Sum _ _) _) (Box _ _ v nvs) =
--  isNeutral v || or [ isNeutral u | (_,u) <- nvs ]
-- isNeutralFill v@(Kan Com VU tbox') box@(Box d x _ _) = do
--   let nK  = nonPrincipal tbox'
--       nJ  = nonPrincipal box
--       nL  = nJ \\ nK
--       aDs = if x `elem` nK then allDirs nL else (x,mirror d):allDirs nL
--   or [ isNeutral (lookBox yc box) | yc <- aDs ]
-- isNeutralFill v@(Kan Fill VU tbox) box =
--   or [ isNeutral (lookBox yc box) | yc <- defBox box \\ defBox tbox ]
-- isNeutralFill v@(VEquivSquare y z _ _ _) box@(Box d x _ _) = do
--   let nJ  = nonPrincipal box
--       nL  = nJ \\ [y,z]
--       aDs = if x `elem` [y,z] then allDirs nL else (x,mirror d) : allDirs nL
--   or [ isNeutral (lookBox yc box) | yc <- aDs ]
-- isNeutralFill v@(VEquivEq z a b f s t) box@(Box d x vx nxs)
--   | d == down && z == x = isNeutral $ app s vx
--   | otherwise           = -- TODO: check
--     let nJ  = nonPrincipal box
--         nL  = nJ \\ [z]
--         aDs = if x == z then allDirs nL else (x,mirror d) : allDirs nL
--     in or [ isNeutral (lookBox yc box) | yc <- aDs ]
-- isNeutralFill v box = False

-- TODO: Simplify?
comps :: Name -> [(Binder,Ter)] -> Env -> [(System Val,Val)] -> [Val]
comps i []         _ []         = []
comps i ((x,a):as) e ((ts,u):tsus) =
  let v  = comp Pos i (eval e a) ts u
      vs = comps i as (Pair e (x,v)) tsus
  in v : vs
comps _ _ _ _ = error "comps: different lengths of types and values"

isNeutral :: Val -> Bool
isNeutral (VVar _ _)        = True
isNeutral (VApp u _)        = isNeutral u
isNeutral (VAppFormula u _) = isNeutral u
isNeutral (VFst v)          = isNeutral v
isNeutral (VSnd v)          = isNeutral v
isNeutral (VSplit _ v)      = isNeutral v
isNeutral (Kan _ a ts u)    = isNeutral a || isNeutralSystem ts || isNeutral u
-- isNeutral (VInhRec _ _ _ v)    = isNeutral v
-- isNeutral (VCircleRec _ _ _ v) = isNeutral v
-- isNeutral (VIntRec _ _ _ _ v)  = isNeutral v
-- isNeutral (VFillN _ _)         = True
-- isNeutral (VComN _ _)          = True
isNeutral _                    = False

isNeutralSystem :: System Val -> Bool
isNeutralSystem = any isNeutral . Map.elems

fill :: Sign -> Name -> Val -> System Val -> Val -> Val
fill Neg i a ts u =  trace "fill Neg" $ (fill Pos i (a `sym` i) (ts `sym` i) u) `sym` i
fill Pos i a ts u =  trace "fill Pos" $
  comp Pos j (a `connect` (i, j)) (ts `connect` (i, j)) u
  where j = fresh (Atom i,a,u,ts)

comp :: Sign -> Name -> Val -> System Val -> Val -> Val
comp Neg i a ts u = trace "comp Neg" $ comp Pos i (a `sym` i) (ts `sym` i) u
-- If 1 is a key of ts, then it means all the information is already there.
-- This is used to take (k = 0) of a comp when k \in L
comp Pos i a ts u | eps `Map.member` ts = (ts ! eps) `act` (i,Dir 1)
comp Pos i vid@(VId a u v) ts w = trace "comp VId"
  Path j $ comp Pos i (a @@ j) ts' (w @@ j)
  where j   = fresh (Atom i, vid, ts, w)
        ts' = insertSystem (j ~> 0) u $
              insertSystem (j ~> 1) v $
              Map.map (@@ j) ts
comp Pos i b@(VSigma a f) ts u = VSPair (fill_u1 `act` (i, Dir 1)) comp_u2
  where (t1s, t2s) = (Map.map fstSVal ts, Map.map sndSVal ts)
        (u1,  u2)  = (fstSVal u, sndSVal u)
        fill_u1    = fill Pos i a t1s u1
        comp_u2    = comp Pos i (app f fill_u1) t2s u2

comp Pos i a@VPi{} ts u   = Kan i a ts u

comp Pos i g@(Glue hisos b) ws wi0 =
    let unglue = UnGlue hisos b
        vs   = Map.mapWithKey (\alpha wAlpha -> app (unglue `face` alpha) wAlpha) ws
        vi0  = app (unglue `face` (i ~> 0)) wi0 -- in b(i0)

        v    = fill Pos i b vs vi0           -- in b
        vi1  = v `face` (i ~> 1)

        hisosI1 = hisos `face` (i ~> 1)
        (hisos', hisos'') = Map.partitionWithKey
                            (\alpha _ -> alpha `Map.member` hisos) hisosI1

        us'    = Map.mapWithKey (\gamma (Hiso aGamma _ _ _ _ _) ->
                  fill Pos i aGamma (ws `face` gamma) (wi0 `face` gamma))
                hisos'
        usi1'  = Map.map (\u -> u `face` (i ~> 1)) us'

        ls'    = Map.mapWithKey (\gamma (Hiso aGamma bGamma fGamma _ _ _) ->
                  pathComp Pos i bGamma (vs `face` gamma)
                    (fGamma `app` (us' ! gamma)) (v `face` gamma))
                 hisos'

        vi1'  = compLine (b `face` (i ~> 1)) ls' vi1

        uls''   = Map.mapWithKey (\gamma hisoGamma@(Hiso aGamma bGamma fGamma _ _ _) ->
                     let shgamma :: System ()
                         shgamma = Map.union (shape hisos') (shape ws) `face` gamma
                         usgamma = Map.mapWithKey (\beta _ ->
                                     let delta = gamma `meet` beta
                                     in if delta `Map.member` ws
                                        then ws `proj` (delta `meet` (i ~> 1))
                                        else usi1' `proj` delta)
                                   shgamma
                     in gradLemma hisoGamma usgamma (vi1' `face` gamma))
                   hisos''

        vi1''   = compLine (b `face` (i ~> 1)) (Map.map snd uls'') vi1'

        usi1    = Map.mapWithKey (\gamma _ ->
                    if gamma `Map.member` usi1' then usi1' ! gamma
                    else fst (uls'' ! gamma))
                  hisosI1

    in glueElem usi1 vi1''

comp Pos i (Kan j VU ejs b) ws wi0 =
    let es    = Map.map (Path j . (`sym` j)) ejs
        hisos = Map.map eqHiso es
        unkan = UnKan hisos b

        vs    = Map.mapWithKey (\alpha wAlpha -> app (unkan `face` alpha) wAlpha) ws
        vi0   = app (unkan `face` (i ~> 0)) wi0 -- in b(i0)

        vi1     = comp Pos i b vs vi0           -- in b

        hisosI1 = hisos `face` (i ~> 1)
        (hisos', hisos'') = Map.partitionWithKey
                            (\alpha _ -> alpha `Map.member` hisos) hisosI1

        usi1'    = Map.mapWithKey (\gamma (Hiso aGamma _ _ _ _ _) ->
                     comp Pos i aGamma (ws `face` gamma) (wi0 `face` gamma))
                   hisos'

        ls'    = Map.mapWithKey (\gamma _ ->
                   pathUniv i (es `proj` gamma) (ws `face` gamma) (wi0 `face` gamma))
                 hisos'

        vi1'  = compLine (b `face` (i ~> 1)) ls' vi1

        uls''   = Map.mapWithKey (\gamma hisoGamma@(Hiso aGamma bGamma fGamma _ _ _) ->
                     let shgamma :: System ()
                         shgamma = Map.union (shape hisos') (shape ws) `face` gamma
                         usgamma = Map.mapWithKey (\beta _ ->
                                     let delta = gamma `meet` beta
                                     in if delta `Map.member` ws
                                        then ws `proj` (delta `meet` (i ~> 1))
                                        else usi1' `proj` delta)
                                   shgamma
                     in gradLemma hisoGamma usgamma (vi1' `face` gamma))
                   hisos''

        vi1''   = compLine (b `face` (i ~> 1)) (Map.map snd uls'') vi1'

        usi1    = Map.mapWithKey (\gamma _ ->
                    if gamma `Map.member` usi1' then usi1' ! gamma
                    else fst (uls'' ! gamma))
                  hisosI1

    in kanUElem usi1 vi1''

comp Pos i VU ts u = Kan i VU ts u

comp Pos i a ts u | isNeutral a || isNeutralSystem ts || isNeutral u = Kan i a ts u
comp Pos i v@(Ter (Sum _ nass) env) tss (VCon n us) = case getIdent n nass of
  Just as -> VCon n $ comps i as env tsus
    where tsus = transposeSystemAndList (Map.map unCon tss) us
  Nothing -> error $ "fill: missing constructor in labelled sum " ++ n

comp Pos i a ts u = error $
  "comp _: not implemented for " <+> show a <+> show ts <+> parens (show u)

-- Lemma 2.1
-- assumes u and u' : A are solutions of us + (i0 -> u(i0)) and u(i0) = u'(i1)
-- (in the Pos case, otherwise we symmetrize)
-- The output is an L-path in A(i1) between u(i1) and u'(i1)
pathComp :: Sign -> Name -> Val -> System Val -> (Val -> Val -> Val)
pathComp Neg i a us u u' =
  pathComp Pos i (a `sym` i) (us `sym` i) (u `sym` i) (u' `sym` i)
pathComp Pos i a us u u' = Path j $ comp Pos i a us' (u `face` (i ~> 0))
  where j   = fresh (Atom i, a, us, u, u')
        us' = insertsSystem [(j ~> 0, u), (j ~> 1, u')] us

-- Lemma 6.1
-- given e (an equality in U), an L-system us (in e0) and ui0 (in e0 (i0))
-- The output is an L-path in e1(i1) between sigma (i1) ui1 and vi1
-- where sigma = HisoProj (ProjSign Pos) e
--       ui1   = comp Pos i (e 1) us ui0
--       vi1   = comp Pos i (e 1) (sigma us) (sigma(i0) ui0)
-- Moreover, if e is constant, so is the output.
pathUniv :: Name -> Val -> System Val -> Val -> Val
pathUniv i e us ui0 = Path k xi1
  where j:k:_ = freshs (Atom i, e, us, ui0)
        f     = HisoProj (HisoSign Pos) e
        ej    = e @@ j
        ui1   = comp Pos i (e @@ Zero) us ui0
        ws    = Map.mapWithKey (\alpha uAlpha ->
                  fill Pos j (ej `face` alpha) Map.empty uAlpha)
                us
        wi0   = fill Pos j (ej `face` (i ~> 0)) Map.empty ui0
        wi1   = comp Pos i ej ws wi0
        wi1'  = fill Pos j (ej `face` (i ~> 1)) Map.empty ui1
        xi1   = comp Pos j (ej `face` (i ~> 1))
                  (insertsSystem [(k ~> 0, wi1'), (k ~> 1, wi1)] Map.empty) ui1


-- Lemma 2.2
-- takes a type A, an L-system of lines ls and a value u
-- s.t. ls alpha @@ 0 = u alpha
-- and returns u' s.t. ls alpha @@ 1 = u' alpha
compLine :: Val -> System Val -> Val -> Val
compLine a ls u = comp Neg i a (Map.map (@@ i) ls) u
  where i = fresh (a, ls, u)

class Convertible a where
  conv :: Int -> a -> a -> Bool

instance Convertible Val where
  conv k VU VU                                  = True
  conv k (Ter (Lam x u) e) (Ter (Lam x' u') e') =
    let v = mkVar k $ support (e, e')
    in conv (k+1) (eval (Pair e (x,v)) u) (eval (Pair e' (x',v)) u')
  conv k (Ter (Lam x u) e) u' =
    let v = mkVar k $ support (e,u')
    in conv (k+1) (eval (Pair e (x,v)) u) (app u' v)
  conv k u' (Ter (Lam x u) e) =
    let v = mkVar k $ support (u',e)
    in conv (k+1) (app u' v) (eval (Pair e (x,v)) u)
  conv k (Ter (Split p _) e) (Ter (Split p' _) e') =
    (p == p') && conv k e e'
  conv k (Ter (Sum p _) e)   (Ter (Sum p' _) e') =
    (p == p') && conv k e e'
  conv k (Ter (PN (Undef p)) e) (Ter (PN (Undef p')) e') =
    (p == p') && conv k e e'
  conv k (VPi u v) (VPi u' v') =
    let w = mkVar k $ support (u,v,u',v')
    in conv k u u' && conv (k+1) (app v w) (app v' w)
  conv k (VId a u v) (VId a' u' v') = and [conv k a a', conv k u u', conv k v v']
  conv k (Path i u) (Path i' u')    = trace "conv Path Path" $
                                      conv k (u `rename` (i,j)) (u' `rename` (i',j))
    where j = fresh (u,u')
  conv k (Path i u) p'              = trace "conv Path p" $
                                      conv k (u `rename` (i,j)) (p' @@ j)
    where j = fresh u
  conv k p (Path i' u')             = trace "conv p Path" $
                                      conv k (p @@ j) (u' `rename` (i',j))
    where j = fresh u'

  conv k (VSigma u v) (VSigma u' v') = conv k u u' && conv (k+1) (app v w) (app v' w)
    where w = mkVar k $ support (u,v,u',v')
  conv k (VFst u) (VFst u')              = conv k u u'
  conv k (VSnd u) (VSnd u')              = conv k u u'
  conv k (VSPair u v)   (VSPair u' v')   = conv k u u' && conv k v v'
  conv k (VSPair u v)   w                =
    conv k u (fstSVal w) && conv k v (sndSVal w)
  conv k w              (VSPair u v)     =
    conv k (fstSVal w) u && conv k (sndSVal w) v

  conv k (VCon c us) (VCon c' us') = (c == c') && and (zipWith (conv k) us us')

  conv k (Kan i a ts u) v' | isRegularConv k i ts = trace "conv Kan regular"
    conv k u v'
  conv k v' (Kan i a ts u) | isRegularConv k i ts = trace "conv Kan regular"
    conv k v' u
  conv k v@(Kan i a ts u) v'@(Kan i' a' ts' u') = trace "conv Kan" $
     let j    = fresh (v, v')
         tsj  = ts  `rename` (i,j)
         tsj' = ts' `rename` (i',j)
     in
     and [ conv k (a `rename` (i,j)) (a' `rename` (i',j))
         , Map.keysSet tsj == Map.keysSet tsj'
         , and $ Map.elems $ Map.intersectionWith (conv k) tsj tsj'
         , conv k (u `rename` (i,j)) (u' `rename` (i',j))]

  conv k (Glue hisos v) (Glue hisos' v') = conv k hisos hisos' && conv k v v'

  conv k (KanUElem us u) v'@(KanUElem us' u') =
    conv k u u' && conv k us (border v' us)
  conv k (KanUElem us u) v'  = conv k u v'
  conv k v (KanUElem us' u') = conv k v u'

  conv k (GlueElem us u) (GlueElem us' u') = conv k us us' && conv k u u'

  conv k (UnKan hisos v) (UnKan hisos' v') = conv k hisos hisos' && conv k v v'
  conv k (UnGlue hisos v) (UnGlue hisos' v') = conv k hisos hisos' && conv k v v'

  conv k u@(HisoProj{}) u'@(HisoProj{}) = conv (k+1) (app u w) (app u' w)
       where w = mkVar k $ support (u,u')

  conv k (VExt phi f g p) (VExt phi' f' g' p') =
    and [phi == phi', conv k f f', conv k g g', conv k p p']

-- conv k (VExt x b f g p) (VExt x' b' f' g' p') =
--   andM [x <==> x', conv k b b', conv k f f', conv k g g', conv k p p']
-- conv k (VHExt x b f g p) (VHExt x' b' f' g' p') =
--   and [x == x', conv k b b', conv k f f', conv k g g', conv k p p']
-- conv k (VInh u) (VInh u')                     = conv k u u'
-- conv k (VInc u) (VInc u')                     = conv k u u'
-- conv k (VSquash x u v) (VSquash x' u' v')     =
--   and [x == x', conv k u u', conv k v v']

-- conv k (Kan Fill v box) (Kan Fill v' box')    =
--   conv k v v' && convBox k box box'
-- conv k (Kan Com v box) (Kan Com v' box')      =
--   and [conv k v v', convBox k (swap box x y) (swap box' x' y)]
--   where y      = fresh ((v,v'),(box,box'))
--         (x,x') = (pname box, pname box')
-- conv k (VComN v box) (VComN v' box')      =
--   and [conv k v v', convBox k (swap box x y) (swap box' x' y)]
--   where y      = fresh ((v,v'),(box,box'))
--         (x,x') = (pname box, pname box')
-- conv k (VFillN v box) (VFillN v' box')      =
--   and [conv k v v', convBox k (swap box x y) (swap box' x' y)]
--   where y      = fresh ((v,v'),(box,box'))
--         (x,x') = (pname box, pname box')
-- conv k (VEquivEq x a b f s t) (VEquivEq x' a' b' f' s' t') =
--   and [x == x', conv k a a', conv k b b',
--        conv k f f', conv k s s', conv k t t']
-- conv k (VEquivSquare x y a s t) (VEquivSquare x' y' a' s' t') =
--   and [x == x', y == y', conv k a a', conv k s s', conv k t t']
-- conv k (VPair x u v) (VPair x' u' v')     =
--   and [x == x', conv k u u', conv k v v']
-- conv k (VSquare x y u) (VSquare x' y' u') =
--   and [x == x', y == y', conv k u u']
-- conv k (VComp box) (VComp box')           =
--   convBox k (swap box x y) (swap box' x' y)
--   where y      = fresh (box,box')
--         (x,x') = (pname box, pname box')
-- conv k (VFill x box) (VFill x' box')      =
--   convBox k (swap box x y) (swap box' x' y)
--   where y      = fresh (box,box')

  conv k (VVar x phis)  (VVar x' phis')  = x == x' && phis == phis'
  conv k (VApp u v)     (VApp u' v')     = conv k u u' && conv k v v'
  conv k (VAppFormula u x) (VAppFormula u' x') = conv k u u' && (x == x')
  conv k (VSplit u v)   (VSplit u' v')   = conv k u u' && conv k v v'
  -- conv k (VInhRec b p phi v) (VInhRec b' p' phi' v') =
  --   and [conv k b b', conv k p p', conv k phi phi', conv k v v']
  -- conv k VCircle        VCircle          = True
  -- conv k VBase          VBase            = True
  -- conv k (VLoop x)      (VLoop y)        = x == y
  -- conv k (VCircleRec f b l v) (VCircleRec f' b' l' v') =
  --   and [conv k f f', conv k b b', conv k l l', conv k v v']
  -- conv k VI             VI               = True
  -- conv k VI0            VI0              = True
  -- conv k VI1            VI1              = True
  -- conv k (VLine x)      (VLine y)        = x == y
  -- conv k (VIntRec f s e l u) (VIntRec f' s' e' l' u') =
  --   and [conv k f f', conv k s s', conv k e e', conv k l l', conv k u u']
  conv k _              _                = False

-- convBox :: Int -> Box Val -> Box Val -> Bool
-- convBox k box@(Box d pn _ ss) box'@(Box d' pn' _ ss') =
--   if (d == d') && (pn == pn') && (sort np == sort np')
--      then and [ conv k (lookBox s box) (lookBox s box')
--               | s <- defBox box ]
--      else False
--   where (np, np') = (nonPrincipal box, nonPrincipal box')


isRegularConv :: Int -> Name -> System Val -> Bool
isRegularConv k i us =
  and $ Map.elems $ Map.map (\u -> conv k u (u `act` (i,Dir 0))) us


instance Convertible Env where
  conv k e e' = and $ zipWith (conv k) (valOfEnv e) (valOfEnv e')

instance (Ord k, Convertible a) => Convertible (Map k a) where
  conv k ts ts' =  Map.keysSet ts == Map.keysSet ts' &&
                   (and $ Map.elems $ Map.intersectionWith (conv k) ts ts')

instance Convertible Hiso where
  conv k (Hiso a b f g s t) (Hiso a' b' f' g' s' t') =
    and [conv k x y | (x, y) <- zip [a, b, f, g, s, t] [a', b', f', g', s', t']]
