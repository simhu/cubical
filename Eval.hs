{-# LANGUAGE CPP #-}
module Eval ( eval
            , evals
            , app
            , (@@)
            , normal
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
look x Empty = error ("look:" <+> x <+> "not found")

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

eval e t@(HSum {})       = Ter t e
eval e (PCon n ts ns t0 t1) =
  let i = fresh e
      -- TODO: lambda abstract or not?
      u0 = eval e (mkLams ns t0)
      u1 = eval e (mkLams ns t1)
  in Path i $ VPCon n (map (eval e) ts) (Atom i) u0 u1
eval e t@(HSplit {})     = Ter t e

evals :: Env -> [(Binder,Ter)] -> [(Binder,Val)]
evals env = map (second (eval env))

pathCon :: Ident -> [Val] -> Formula -> Val -> Val -> Val
pathCon n vs (Dir Zero) u _ = apps u vs
pathCon n vs (Dir One)  _ u = apps u vs
pathCon n vs phi        u v = VPCon n vs phi u v

fstSVal, sndSVal :: Val -> Val
fstSVal (VSPair a b)    = a
fstSVal (KanUElem _ u)  = fstSVal u  -- TODO: check this!
fstSVal u | isNeutral u = VFst u
          | otherwise   = error $ "fstSVal: " ++ show u ++ " should be neutral"
sndSVal (VSPair a b)    = b
sndSVal (KanUElem _ u)  = sndSVal u  -- TODO: check this!
sndSVal u | isNeutral u = VSnd u
          | otherwise   = error $ "sndSVal: " ++show u ++ " should be neutral"

instance Nominal Val where
  support VU                            = []
  support (Ter _ e)                     = support e
  support (VPi v1 v2)                   = support [v1,v2]
  support (Kan i a ts u)                = i `delete` support (a,ts,u)
  support (KanNe i a ts u)              = i `delete` support (a,ts,u)
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
  support (GlueLine ts u phi)           = support (ts,u,phi)
  support (GlueLineElem ts u phi)       = support (ts,u,phi)

  support (VExt phi f g p)              = support (phi,f,g,p)

  support VCircle                       = []
  support VBase                         = []
  support (VLoop phi)                   = support phi
  support (VCircleRec f b l s)          = support (f,b,l,s)

  support (VInh v)                      = support v
  support (VInc v)                      = support v
  support (VSquash phi v0 v1)           = support (phi,v0,v1)
  support (VInhRec b p h a)             = support (b,p,h,a)

  support (VPCon _ vs phi u v)          = support (vs,phi,u,v)
  support (VHSplit u v)                 = support (u,v)

  -- support (VExt x b f g p)           = support (x, [b,f,g,p])
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
  -- support VI                            = []
  -- support VI0                           = []
  -- support VI1                           = []
  -- support (VIntRec f s e l u)           = support (f,s,e,l,u)
  -- support (VLine n)                     = [n]
  -- support v                             = error ("support " ++ show v)


  act u (i, phi) = -- trace ("act" <+> show u <+> parens (show i <+> "=" <+> show phi)) $
    let acti :: Nominal a => a -> a
        acti u = act u (i, phi)
    in case u of
         VU      -> VU
         Ter t e -> Ter t (acti e)
         VPi a f -> VPi (acti a) (acti f)
         Kan j a ts v -> comp Pos k (ar a) (ar ts) (ar v)
              where k   = fresh (u, Atom i, phi)
                    ar :: Nominal a => a -> a
                    ar = acti . (`swap` (j,k))
         -- TODO: Check that act on neutral is neutral
         KanNe j a ts v -> KanNe k (ar a) (ar ts) (ar v)
              where k   = fresh (u, Atom i, phi)
                    ar :: Nominal a => a -> a
                    ar = acti . (`swap` (j,k))

         KanUElem ts u -> kanUElem (acti ts) (acti u)
         UnKan ts u    -> UnKan (acti ts) (acti u)

         VId a u v -> VId (acti a) (acti u) (acti v)
         Path j v -> Path k (acti (v `swap` (j,k)))
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
         GlueLine ts u psi -> glueLine (acti ts) (acti u) (acti psi)
         GlueLineElem ts u psi -> glueLineElem (acti ts) (acti u) (acti psi)

         VExt psi f g p -> vext (acti psi) (acti f) (acti g) (acti p)

         VCircle    -> VCircle
         VBase      -> VBase
         VLoop psi  -> loop (acti psi)
         VCircleRec f b l s -> circleRec (acti f) (acti b) (acti l) (acti s)

         VInh v                -> VInh (acti v)
         VInc v                -> VInc (acti v)
         VSquash psi v0 v1     -> squash (acti psi) (acti v0) (acti v1)
         VInhRec b p h a       -> inhRec (acti b) (acti p) (acti h) (acti a)

         VPCon n vs phi u v -> pathCon n (acti vs) (acti phi) (acti u) (acti v)
         VHSplit u v        -> app (acti u) (acti v)

  -- This increases efficiency as it won't trigger computation.
  swap u ij@ (i,j) =
    let sw :: Nominal a => a -> a
        sw u = swap u ij
    in case u of
         VU      -> VU
         Ter t e -> Ter t (sw e)
         VPi a f -> VPi (sw a) (sw f)
         Kan k a ts v -> Kan (swapName k ij) (sw a) (sw ts) (sw v)
         KanNe k a ts v -> KanNe (swapName k ij) (sw a) (sw ts) (sw v)

         KanUElem ts u -> KanUElem (sw ts) (sw u)
         UnKan ts u    -> UnKan (sw ts) (sw u)

         VId a u v -> VId (sw a) (sw u) (sw v)
         Path k v -> Path (swapName k ij) (sw v)

         VSigma a f -> VSigma (sw a) (sw f)
         VSPair u v -> VSPair (sw u) (sw v)
         VFst u     -> VFst (sw u)
         VSnd u     -> VSnd (sw u)

         VCon c vs  -> VCon c (sw vs)

         VVar x psis       -> VVar x (sw psis)
         VAppFormula u psi -> VAppFormula (sw u) (sw psi)
         VApp u v          -> VApp (sw u) (sw v)
         VSplit u v        -> VSplit (sw u) (sw v)

         Glue ts u         -> Glue (sw ts) (sw u)
         UnGlue ts u       -> UnGlue (sw ts) (sw u)
         GlueElem ts u     -> GlueElem (sw ts) (sw u)
         HisoProj n e      -> HisoProj n (sw e)
         GlueLine ts u psi -> GlueLine (sw ts) (sw u) (sw psi)
         GlueLineElem ts u psi -> GlueLineElem (sw ts) (sw u) (sw psi)

         VExt psi f g p -> VExt (sw psi) (sw f) (sw g) (sw p)

         VCircle    -> VCircle
         VBase      -> VBase
         VLoop psi  -> VLoop (sw psi)
         VCircleRec f b l s -> VCircleRec (sw f) (sw b) (sw l) (sw s)

         VInh v            -> VInh (sw v)
         VInc v            -> VInc (sw v)
         VSquash phi v0 v1 -> VSquash (sw phi) (sw v0) (sw v1)
         VInhRec b p h a   -> VInhRec (sw b) (sw p) (sw h) (sw a)

         VPCon n vs phi u v -> pathCon n (sw vs) (sw phi) (sw u) (sw v)
         VHSplit u v        -> VHSplit (sw u) (sw v)

instance Nominal Hiso where
  support (Hiso a b f g s t)  = support (a,b,f,g,s,t)

  act (Hiso a b f g s t) iphi = Hiso a' b' f' g' s' t'
    where (a',b',f',g',s',t') = act (a,b,f,g,s,t) iphi

  swap (Hiso a b f g s t) ij = Hiso a' b' f' g' s' t'
    where (a',b',f',g',s',t') = swap (a,b,f,g,s,t) ij

instance Nominal Env where
  support Empty          = []
  support (Pair e (_,v)) = support (e, v)
  support (PDef _ e)     = support e

  act e iphi  = mapEnv (`act` iphi) e

  swap e ij = mapEnv (`swap` ij) e

-- Glueing
glue :: System Hiso -> Val -> Val
glue hisos b | Map.null hisos         = b
glue hisos b | eps `Map.member` hisos = hisoA (hisos ! eps)
glue hisos b = Glue hisos b

glueElem :: System Val -> Val -> Val
glueElem us v | Map.null us         = v
glueElem us v | eps `Map.member` us = us ! eps
glueElem us v = GlueElem us v

glueLine :: System () -> Val -> Formula -> Val
glueLine ts b (Dir Zero) = b
glueLine ts b (Dir One)  = glue hisos b
  where hisos = Map.mapWithKey (\alpha _ -> idHiso (b `face` alpha)) ts
glueLine ts b phi = GlueLine ts b phi

idHiso :: Val -> Hiso
idHiso a = Hiso a a idV idV refl refl
  where idV  = Ter (Lam (noLoc "x") (Var "x")) Empty
        refl = Ter (Lam (noLoc "x") (App (App (PN Refl) (Var "y")) (Var "x")))
                 (Pair Empty ((noLoc "y"),a))

glueLineElem :: System () -> Val -> Formula -> Val
glueLineElem ts v (Dir Zero) = v
glueLineElem ts v (Dir One)  = glueElem (border v ts) v
glueLineElem ts v phi        = GlueLineElem ts  v phi

unGlueLineElem :: Formula -> Val -> Val
unGlueLineElem (Dir Zero) v                    = v
unGlueLineElem (Dir One)  (GlueElem _ v)       = v
unGlueLineElem phi        (GlueLineElem _ v _) = v
unGlueLineElem phi        v = error $ "unGlueLineElem: " <+> show phi <+> show v

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

loop :: Formula -> Val
loop (Dir _) = VBase
loop phi     = VLoop phi

circleRec :: Val -> Val -> Val -> Val -> Val
circleRec _ b _ VBase         = b
circleRec f b l v@(VLoop phi) = l @@ phi
circleRec f b l v@(Kan i VCircle us u) = comp Pos j ffillu us' u'
  where j    = fresh (f,b,l,v)
        usij = us `swap` (i,j)
        us'  = Map.mapWithKey crec usij
        u'   = crec (i ~> 0) u
        ffillu     = app f (fill Pos j VCircle usij u)
        crec alpha = circleRec (f `face` alpha)
                       (b `face` alpha) (l `face` alpha)
circleRec f b l (KanUElem _ u) = circleRec f b l u
circleRec f b l v = VCircleRec f b l v -- v should be neutral

squash :: Formula -> Val -> Val -> Val
squash (Dir Zero) u _ = u
squash (Dir One)  _ v = v
squash phi        u v = VSquash phi u v

inhRec :: Val -> Val -> Val -> Val -> Val
inhRec b p f (KanUElem _ u) = inhRec b p f u
inhRec b p f (VInc a) = app f a
inhRec b p f (VSquash phi u0 u1) =
  app (app p (inhRec b p f u0)) (inhRec b p f u1) @@ phi
inhRec b p f a = VInhRec b p f a -- a should be neutral

-- Application
app :: Val -> Val -> Val
app (Ter (Lam x t) e) u            = eval (Pair e (x,u)) t
app kan@(Kan i b@(VPi a f) ts li0) ui1 =
  trace ("app (Kan VPi)") $
    let j   = fresh (kan,ui1)
        (aj,fj,tsj) = (a,f,ts) `swap` (i,j)
        u   = fill Neg j aj Map.empty ui1
        ui0 = u `face` (j ~> 0)
    in comp Pos j (app fj u)
           (Map.intersectionWith app tsj (border u tsj))
           (app li0 ui0)
app u@(Ter (Split _ _) _) (KanUElem _ v) = app u v
app (Ter (Split _ nvs) e) (VCon name us) = case lookup name nvs of
  Just (xs,t)  -> eval (upds e (zip xs us)) t
  Nothing -> error $ "app: Split with insufficient arguments; " ++
                        "missing case for " ++ name


-- TODO: is this correct even for HITs???
app u@(Ter (HSplit _ _ hbr) e) (KanUElem _ v) = app u v

app (Ter (HSplit _ _ hbr) e) (VCon name us) =
  case lookup name (zip (map hBranchToLabel hbr) hbr) of
    Just (Branch _ xs t)  -> eval (upds e (zip xs us)) t
    _ -> error ("app: HSplit with insufficient arguments;"
                <+> "missing case for " <+> name)

app (Ter (HSplit _ _ hbr) e) (VPCon name us phi _ _) =
  case lookup name (zip (map hBranchToLabel hbr) hbr) of
    Just (HBranch _ xs t) -> eval (upds e (zip xs us)) t @@ phi
    _ -> error ("app: HSplit with insufficient arguments;"
                <+> "missing case for " <+> name)

app u@(Ter (HSplit _ f hbr) e) kan@(Kan i v ws w) = -- v should be corr. hsum
  let j     = fresh (e,kan)
      wsij  = ws `swap` (i,j)
      ws'   = Map.mapWithKey (\alpha -> app (u `face` alpha)) wsij
      w'    = app (u `face` (i ~> 0)) w
      ffill = app (eval e f) (fill Pos j (v `swap` (i,j)) wsij w)
  in comp Pos j ffill ws' w'

app g@(UnGlue hisos b) w
    | Map.null hisos         = w
    | eps `Map.member` hisos = app (hisoF (hisos ! eps)) w
    | otherwise              = case w of
       GlueElem us v -> v
       KanUElem _ v  -> app g v
       _             -> VApp g w

app g@(UnKan hisos b) w
    | Map.null hisos         = w
    | eps `Map.member` hisos = app (hisoF (hisos ! eps)) w
    | otherwise              = kanUElem (Map.mapWithKey (\alpha hisoAlpha ->
                                 app (hisoF hisoAlpha) (w `face` alpha))
                               hisos) w

-- TODO: recheck at least 2 more times (please decrease the counter if
-- you checked)
app (HisoProj hisoProj e) u = trace "app HisoProj" $
  case hisoProj of
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
app u@(Ter (HSplit _ _ _) _) v
  | isNeutral v = VHSplit u v -- v should be neutral
  | otherwise   = error $ "app: (VHSplit) " ++ show v ++ " is not neutral"
app u@(VExt phi f g p) v = (app p v) @@ phi
app r s
 | isNeutral r = VApp r s -- r should be neutral
 | otherwise   = error $ "app: (VApp) " ++ show r ++ " is not neutral"

apps :: Val -> [Val] -> Val
apps = foldl app

(@@) :: ToFormula a => Val -> a -> Val
(Path i u) @@ phi = u `act` (i, toFormula phi)
v @@ phi          = VAppFormula v (toFormula phi)


-- Grad Lemma, takes a iso an L-system ts a value v s.t. sigma us = border v
-- outputs u s.t. border u = us and an L-path between v and sigma u
-- an theta is a L path if L-border theta is constant
gradLemma :: Hiso -> System Val -> Val -> (Val, Val)
gradLemma hiso@(Hiso a b f g s t) us v =
  trace ("gradLemma \n b = " ++ show b ++ "\n v = " ++ show v)
    (u, Path i theta'')
  where i:j:_   = freshs (hiso, us, v)
        us'     = Map.mapWithKey (\alpha uAlpha ->
                                   app (t `face` alpha) uAlpha @@ i) us
        theta   = fill Pos i a us' (app g v)
        u       = theta `face` (i ~> 1)
        ws      = insertSystem (i ~> 0) (app g v) $
                  insertSystem (i ~> 1) (app t u @@ j) $
                  Map.mapWithKey
                    (\alpha uAlpha ->
                      app (t `face` alpha) uAlpha @@ (Atom i :/\: Atom j)) us
        theta'  = comp Neg j a ws theta
        xs      = insertSystem (i ~> 0) (app s v @@ j) $
                  insertSystem (i ~> 1) (app s (app f u) @@ j) $
                  Map.mapWithKey
                    (\alpha uAlpha ->
                      app (s `face` alpha) (app (f `face` alpha) uAlpha) @@ j) us
        theta'' = comp Pos j b xs (app f theta')


-- any equality defines an equivalence Lemma 4.2
eqLemma :: Val -> System Val -> Val -> (Val, Val)
eqLemma e ts a = trace ("eqLemma " ++ show a) $ (t, Path j theta'')
  where i:j:_  = freshs (e, ts, a)
        ei      = e @@ i
        vs      = Map.mapWithKey (\alpha uAlpha ->
                    fill Pos i (ei `face` alpha) Map.empty uAlpha) ts
        theta   = fill Neg i ei vs a
        --t       = comp Neg i ei vs a
        t       = theta `face` (i ~> 0)
        theta'  = fill Pos i ei Map.empty t
        ws      = insertSystem (j ~> 1) theta' $
                  insertSystem (j ~> 0) theta $ vs
        theta'' = comp Pos i ei ws t


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
evalPN (i:_) Sym           [_,_,_,p]     = Path i $ p @@ (NegAtom i)
evalPN (i:_) TransU        [_,_,p,t]     = trace ("evalPN TransU") $
                                           comp Pos i (p @@ i) Map.empty t
evalPN (i:_) TransInvU     [_,_,p,t]     = trace "evalPN TransInvU" $
                                           comp Neg i (p @@ i) Map.empty t
evalPN (i:j:_) CSingl [_,_,_,p] = trace "CSingl"
                                  Path i $ VSPair q (Path j (q `connect` (i,j)))
  where q = p @@ i
evalPN (i:_) Ext [_,_,f,g,p] = Path i $ VExt (Atom i) f g p
evalPN _       Inh        [a]           = VInh a
evalPN _       Inc        [_,t]         = VInc t
evalPN (i:_)   Squash     [_,r,s]       = Path i $ VSquash (Atom i) r s
evalPN _       InhRec     [_,b,p,phi,a] = inhRec b p phi a
evalPN (i:_)   IsoId    [a,b,f,g,s,t]   =
  Path i $ Glue (mkSystem [(i ~> 0, Hiso a b f g s t)]) b
evalPN (i:j:_) IsoIdRef [a] =
  Path j $ Path i $ GlueLine (mkSystem [(i ~> 0,())]) a (Atom j)
evalPN (i:_)   MapOnPath  [_,_,f,_,_,p]    = Path i $ app f (p @@ i)
evalPN (i:_)   MapOnPathD [_,_,f,_,_,p]    = Path i $ app f (p @@ i)
evalPN (i:_)   AppOnPath [_,_,_,_,_,_,p,q] = Path i $ app (p @@ i) (q @@ i)
evalPN (i:_)   MapOnPathS [_,_,_,f,_,_,p,_,_,q] =
  Path i $ app (app f (p @@ i)) (q @@ i)
evalPN _       Circle     []               = VCircle
evalPN _       Base       []               = VBase
evalPN (i:_)   Loop       []               = Path i $ VLoop (Atom i)
evalPN _       CircleRec  [f,b,l,s]        = circleRec f b l s
-- evalPN _       I          []               = VI
-- evalPN _       I0         []               = VI0
-- evalPN _       I1         []               = VI1
-- evalPN (x:_)   Line       []               = Path x $ VLine x
-- evalPN _       IntRec     [f,s,e,l,u]      = intrec f s e l u
evalPN _       u          _                = error ("evalPN " ++ show u)

comps :: Name -> [(Binder,Ter)] -> Env -> [(System Val,Val)] -> [Val]
comps i []         _ []         = []
comps i ((x,a):as) e ((ts,u):tsus) =
  let v  = fill Pos i (eval e a) ts u
      vi0 = v `face` (i ~> 1)
      vs  = comps i as (Pair e (x,v)) tsus
  in vi0 : vs
comps _ _ _ _ = error "comps: different lengths of types and values"

isNeutral :: Val -> Bool
isNeutral (VVar _ _)             = True
isNeutral (VApp u _)             = isNeutral u
isNeutral (VAppFormula u _)      = isNeutral u
isNeutral (VFst v)               = isNeutral v
isNeutral (VSnd v)               = isNeutral v
isNeutral (VSplit _ v)           = isNeutral v
isNeutral (Kan _ a ts u)         = -- TODO: Maybe remove?
  isNeutral a || isNeutralSystem ts || isNeutral u
isNeutral (VCircleRec _ _ _ v)   = isNeutral v
isNeutral (KanUElem _ u)         = isNeutral u  -- TODO: check this!
isNeutral (VInhRec _ _ _ v)      = isNeutral v
isNeutral (KanNe _ _ _ _)        = True
isNeutral (VHSplit _ v)        = isNeutral v
-- isNeutral (VIntRec _ _ _ _ v) = isNeutral v
isNeutral _                      = False

isNeutralSystem :: System Val -> Bool
isNeutralSystem = any isNeutral . Map.elems

fill :: Sign -> Name -> Val -> System Val -> Val -> Val
fill Neg i a ts u =  trace "fill Neg" $
  (fill Pos i (a `sym` i) (ts `sym` i) u) `sym` i
fill Pos i a ts u =  trace "fill Pos" $
  comp Pos j (a `connect` (i, j)) (ts `connect` (i, j)) u
  where j = fresh (Atom i,a,u,ts)

comp :: Sign -> Name -> Val -> System Val -> Val -> Val
comp sign i a ts u | i `notElem` support (a,ts) =
   trace "comp cheaply regular" u
-- Another possible optimization:
-- comp sign i a ts u | i `notElem` support a && not (Map.null indep) =
--   trace "comp filter"  comp sign i a ts' u
--   where (ts',indep) = Map.partition (\t -> i `elem` support t) ts
comp Neg i a ts u = trace "comp Neg" $ comp Pos i (a `sym` i) (ts `sym` i) u

-- If 1 is a key of ts, then it means all the information is already there.
-- This is used to take (k = 0) of a comp when k \in L
comp Pos i a ts u | eps `Map.member` ts = (ts ! eps) `act` (i,Dir 1)
comp Pos i (KanUElem _ a) ts u = comp Pos i a ts u
comp Pos i vid@(VId a u v) ts w = trace "comp VId" $
    Path j $ comp Pos i (a @@ j) ts' (w @@ j)
  where j   = fresh (Atom i, vid, ts, w)
        ts' = insertSystem (j ~> 0) u $
              insertSystem (j ~> 1) v $
              Map.map (@@ j) ts
comp Pos i b@(VSigma a f) ts u = trace "comp VSigma"
  VSPair ui1 comp_u2
  where (t1s, t2s) = (Map.map fstSVal ts, Map.map sndSVal ts)
        (u1,  u2)  = (fstSVal u, sndSVal u)
        fill_u1    = fill Pos i a t1s u1
        ui1        = fill_u1 `face` (i ~> 1)
        comp_u2    = comp Pos i (app f fill_u1) t2s u2

comp Pos i a@VPi{} ts u   = Kan i a ts u

comp Pos i g@(Glue hisos b) ws wi0 =
  trace ("comp Glue \n ShapeOk: " ++ show (shape usi1 == shape hisosI1))
    glueElem usi1 vi1''
  where unglue = UnGlue hisos b
        vs   = Map.mapWithKey
                 (\alpha wAlpha -> app (unglue `face` alpha) wAlpha) ws
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
                         shgamma = (shape hisos' `unionSystem` shape ws) `face` gamma
                         usgamma = Map.mapWithKey
                           (\beta _ ->
                             let delta = gamma `meet` beta
                             in if delta `leqSystem` ws
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

comp Pos i t@(Kan j VU ejs b) ws wi0 =
    let es    = Map.map (Path j . (`sym` j)) ejs
        hisos = Map.map eqHiso es
        unkan = UnKan hisos b

        vs    = Map.mapWithKey (\alpha wAlpha -> app (unkan `face` alpha) wAlpha) ws
        vi0   = app (unkan `face` (i ~> 0)) wi0 -- in b(i0)

        vi1     =  comp Pos i b vs vi0           -- in b(i1)

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
                         shgamma = (shape hisos' `unionSystem` shape ws) `face` gamma
                         usgamma =
                           Map.mapWithKey
                             (\beta _ ->
                               let delta = gamma `meet` beta
                               in if delta `leqSystem` ws
                                  then ws `proj` (delta `meet` (i ~> 1))
                                  else usi1' `proj` delta)
                             shgamma
                     in eqLemma (es `proj` (gamma `meet` (i ~> 1)))
                          usgamma (vi1' `face` gamma)) hisos''

        vi1''   = compLine (b `face` (i ~> 1)) (Map.map snd uls'') vi1'

        usi1    = Map.mapWithKey (\gamma _ ->
                    if gamma `Map.member` usi1' then usi1' ! gamma
                    else fst (uls'' ! gamma))
                  hisosI1

    in trace ("comp Kan VU\n Shape Ok: " ++ show (shape usi1 == shape hisosI1)) $
     kanUElem usi1 vi1''

comp Pos i VU ts u = Kan i VU ts u

comp Pos i (GlueLine shape b phi) us u = trace "comp GlueLine"
  glueLineElem shapei1 v phii1
  where shapei1 = shape `face` (i ~> 1)
        phii1   = phi `face` (i ~> 1)
        v = comp Pos i b ws w
        ws = Map.mapWithKey (\alpha uAlpha ->
                              unGlueLineElem (phi `face` alpha) uAlpha) us
        w  = unGlueLineElem (phi `face` (i ~> 0)) u

comp Pos i VCircle ts u = Kan i VCircle ts u

comp Pos i v@(Ter (Sum _ _) _) tss (KanUElem _ w) = comp Pos i v tss w

comp Pos i a ts u | isNeutral a || isNeutralSystem ts || isNeutral u =
  trace "comp Neutral"
  -- ++ show a ++ "\n i=" ++ show i ++ "\n ts = " ++ show ts ++ "\n u = " ++ show u)
  KanNe i a ts u

comp Pos i v@(Ter (Sum _ nass) env) tss (VCon n us) = trace "comp Sum" $
  case getIdent n nass of
  Just as -> VCon n $ comps i as env tsus
    where tsus = transposeSystemAndList (Map.map unCon tss) us
  Nothing -> error $ "fill: missing constructor in labelled sum " ++ n

-- TODO: comp whenever possible (like Sum, but more testing)
comp Pos i v@(Ter (HSum _ _) _) us u = trace "comp HSum" $ Kan i v us u

comp Pos i a ts u =
  error $
  "comp _: not implemented for \n a = " <+> show a <+> "\n" <+>
  "ts = " <+> show ts <+> "\n" <+>
  "u = " <+> parens (show u)

-- Lemma 2.1
-- assumes u and u' : A are solutions of us + (i0 -> u(i0))
-- (in the Pos case, otherwise we symmetrize)
-- The output is an L-path in A(i1) between u(i1) and u'(i1)
pathComp :: Sign -> Name -> Val -> System Val -> (Val -> Val -> Val)
pathComp Neg i a us u u' =
  pathComp Pos i (a `sym` i) (us `sym` i) (u `sym` i) (u' `sym` i)
pathComp Pos i a us u u' = trace "pathComp"
                           Path j $ comp Pos i a us' (u `face` (i ~> 0))
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
-- s.t. ls alpha @@ 1 = u alpha
-- and returns u' s.t. ls alpha @@ 0 = u' alpha
compLine :: Val -> System Val -> Val -> Val
compLine a ls u = trace ("compLine \n a=" ++ show a ++ "\n u = " ++ show u)
  comp Pos i a (Map.map (@@ i) ls) u  -- TODO also check pathComp; are
                                      -- the dirs correct?
  where i = fresh (a, ls, u)

class Convertible a where
  conv   :: Int -> a -> a -> Bool

instance Convertible Val where
  conv k VU VU                                  = True
  conv k w@(Ter (Lam x u) e) w'@(Ter (Lam x' u') e') =
    let v = mkVar k $ support (e, e')
    in trace ("conv Lam Lam \n w = " ++ show w ++ " \n w' = " ++ show w')
     conv (k+1) (eval (Pair e (x,v)) u) (eval (Pair e' (x',v)) u')
  conv k w@(Ter (Lam x u) e) u' =
    let v = mkVar k $ support (e,u')
    in trace ("conv Lam u' \n w = " ++ show w ++ " \n u' = " ++ show u')
        conv (k+1) (eval (Pair e (x,v)) u) (app u' v)
  conv k u' w'@(Ter (Lam x u) e) =
    let v = mkVar k $ support (u',e)
    in trace ("conv u' Lam \n u' = " ++ show u' ++ " \n w' = " ++ show w')
       conv (k+1) (app u' v) (eval (Pair e (x,v)) u)
  conv k (Ter (Split p _) e) (Ter (Split p' _) e') =
    p == p' && conv k e e'
  conv k (Ter (Sum p _) e)   (Ter (Sum p' _) e') =
    p == p' && conv k e e'
  conv k (Ter (PN (Undef p)) e) (Ter (PN (Undef p')) e') =
    p == p' && conv k e e'
  conv k (Ter (HSum p _) e)   (Ter (HSum p' _) e') =
    p == p' && conv k e e'
  conv k (Ter (HSplit p _ _) e) (Ter (HSplit p' _ _) e') =
    p == p' && conv k e e'
  conv k (VPCon c us phi _ _) (VPCon c' us' phi' _ _) =
    -- TODO: can we ignore the faces?
    c == c' && conv k (us,phi) (us',phi')
  conv k (VPi u v) (VPi u' v') =
    let w = mkVar k $ support (u,v,u',v')
    in conv k u u' && conv (k+1) (app v w) (app v' w)

  conv k (VId a u v) (VId a' u' v') = conv k (a,u,v) (a',u',v')
  conv k v@(Path i u) v'@(Path i' u')    =
    trace "conv Path Path" conv k (u `swap` (i,j)) (u' `swap` (i',j))
    where j = fresh (v,v')
  conv k v@(Path i u) p'              = trace "conv Path p" $
                                      conv k (u `swap` (i,j)) (p' @@ j)
    where j = fresh (v,p')
  conv k p v'@(Path i' u')             = trace "conv p Path" $
                                      conv k (p @@ j) (u' `swap` (i',j))
    where j = fresh (p,v')

  conv k (VSigma u v) (VSigma u' v') = conv k u u' && conv (k+1) (app v w) (app v' w)
    where w = mkVar k $ support (u,v,u',v')
  conv k (VFst u) (VFst u')              = conv k u u'
  conv k (VSnd u) (VSnd u')              = conv k u u'
  conv k (VSPair u v)   (VSPair u' v')   = conv k (u,v) (u',v')
  conv k (VSPair u v)   w                =
    conv k u (fstSVal w) && conv k v (sndSVal w)
  conv k w              (VSPair u v)     =
    conv k (fstSVal w) u && conv k (sndSVal w) v

  conv k (VCon c us) (VCon c' us') = c == c' && conv k us us'

  conv k (Kan i a ts u) v' | isIndep k i (a,ts) = trace "conv Kan regular"
    conv k u v'
  conv k v' (Kan i a ts u) | isIndep k i (a,ts) = trace "conv Kan regular"
    conv k v' u
  conv k v@(Kan i a ts u) v'@(Kan i' a' ts' u') = trace "conv Kan" $
     let j    = fresh (v, v')
         tsj  = ts  `swap` (i,j)
         tsj' = ts' `swap` (i',j)
     in
     and [ conv k (a `swap` (i,j)) (a' `swap` (i',j))
         , Map.keysSet tsj == Map.keysSet tsj'
         , and $ Map.elems $ Map.intersectionWith (conv k) tsj tsj'
         , conv k (u `swap` (i,j)) (u' `swap` (i',j))]

  conv k (KanNe i a ts u) v' | isIndep k i (a,ts) = trace "conv KanNe regular"
    conv k u v'
  conv k v' (KanNe i a ts u) | isIndep k i (a,ts) = trace "conv KanNe regular"
    conv k v' u
  conv k v@(KanNe i a ts u) v'@(KanNe i' a' ts' u') = trace "conv KanNe" $
     let j    = fresh (v, v')
         tsj  = ts  `swap` (i,j)
         tsj' = ts' `swap` (i',j)
     in
     and [ conv k (a `swap` (i,j)) (a' `swap` (i',j))
         , Map.keysSet tsj == Map.keysSet tsj'
         , and $ Map.elems $ Map.intersectionWith (conv k) tsj tsj'
         , conv k (u `swap` (i,j)) (u' `swap` (i',j))]


  conv k (Glue hisos v) (Glue hisos' v') = conv k hisos hisos' && conv k v v'

  conv k (KanUElem us u) v'@(KanUElem us' u') =
    conv k u u' && conv k us (border v' us)
  conv k (KanUElem us u) v'  = conv k u v'
  conv k v (KanUElem us' u') = conv k v u'

  conv k (GlueElem us u) (GlueElem us' u') = conv k us us' && conv k u u'

  conv k (GlueLine ts u phi) (GlueLine ts' u' phi') =
    conv k (ts,u,phi) (ts',u',phi')
  conv k (GlueLineElem ts u phi) (GlueLineElem ts' u' phi') =
    conv k (ts,u,phi) (ts',u',phi')

  conv k (UnKan hisos v) (UnKan hisos' v') = conv k hisos hisos' && conv k v v'
  conv k (UnGlue hisos v) (UnGlue hisos' v') = conv k hisos hisos' && conv k v v'

  conv k u@(HisoProj{}) u'@(HisoProj{}) = conv (k+1) (app u w) (app u' w)
       where w = mkVar k $ support (u,u')

  conv k (VExt phi f g p) (VExt phi' f' g' p') =
    conv k (phi,f,g,p) (phi',f',g',p')

  conv k u@(VExt phi f g p) u' = conv (k+1) (app u w) (app u' w)
    where w = mkVar k $ support (u,u')

  conv k u u'@(VExt phi f g p) = conv (k+1) (app u w) (app u' w)
    where w = mkVar k $ support (u,u')

  conv k (VInh u) (VInh u')                     = conv k u u'
  conv k (VInc u) (VInc u')                     = conv k u u'
  conv k (VSquash phi u v) (VSquash phi' u' v') =
    and [conv k phi phi', conv k u u', conv k v v']

  conv k (VVar x phis)  (VVar x' phis')  =
    x == x' && conv k phis phis'
  conv k (VApp u v)     (VApp u' v')     = conv k u u' && conv k v v'
  conv k (VAppFormula u x) (VAppFormula u' x') = conv k u u' && (x == x')
  conv k (VSplit u v)   (VSplit u' v')   = conv k u u' && conv k v v'
  conv k (VHSplit u v)  (VHSplit u' v')  = conv k u u' && conv k v v'
  conv k VCircle        VCircle          = True
  conv k VBase          VBase            = True
  conv k (VLoop phi)    (VLoop phi')     = conv k phi phi'
  conv k (VCircleRec f b l v) (VCircleRec f' b' l' v') =
    and [conv k f f', conv k b b', conv k l l', conv k v v']
  conv k (VInhRec b p f v) (VInhRec b' p' f' v') =
     and [conv k b b', conv k p p', conv k f f', conv k v v']
  -- conv k VI             VI               = True
  -- conv k VI0            VI0              = True
  -- conv k VI1            VI1              = True
  -- conv k (VLine x)      (VLine y)        = x == y
  -- conv k (VIntRec f s e l u) (VIntRec f' s' e' l' u') =
  --   and [conv k f f', conv k s s', conv k e e', conv k l l', conv k u u']
  conv k _              _                = False


isIndep :: (Nominal a, Convertible a) => Int -> Name -> a -> Bool
isIndep k i u = conv k u (u `face` (i ~> 0))

instance Convertible () where conv _ _ _ = True

instance (Convertible a, Convertible b) => Convertible (a, b) where
  conv k (u, v) (u', v') = conv k u u' && conv k v v'

instance (Convertible a, Convertible b, Convertible c)
      => Convertible (a, b, c) where
  conv k (u, v, w) (u', v', w') = and [conv k u u', conv k v v', conv k w w']

instance (Convertible a,Convertible b,Convertible c,Convertible d)
      => Convertible (a,b,c,d) where
  conv k (u,v,w,x) (u',v',w',x') = conv k (u,v,(w,x)) (u',v',(w',x'))

instance Convertible a => Convertible [a] where
  conv k us us' = length us == length us' && and [conv k u u' | (u,u') <- zip us us']

instance Convertible Env where
  conv k e e' = and $ zipWith (conv k) (valOfEnv e) (valOfEnv e')

instance (Ord k, Convertible a) => Convertible (Map k a) where
  conv k ts ts' =  Map.keysSet ts == Map.keysSet ts' &&
                   (and $ Map.elems $ Map.intersectionWith (conv k) ts ts')

instance Convertible Hiso where
  conv k (Hiso a b f g s t) (Hiso a' b' f' g' s' t') =
    conv k [a,b,f,g,s,t] [a',b',f',g',s',t']

instance Convertible Formula where
  conv _ phi psi = sort (invFormula phi 1) == sort (invFormula psi 1)


class Normal a where
  normal :: Int -> a -> a

-- Does neither normalize formulas nor environments.
instance Normal Val where
  normal _ VU = VU
  normal k (Ter (Lam x u) e) = VLam name $ normal (k+1) (eval (Pair e (x,v)) u)
    where v@(VVar name _) = mkVar k $ support e
  normal k (VPi u v) = VPi (normal k u) (normal k v)
  normal k (Kan i u vs v) = comp Pos i (normal k u) (normal k vs) (normal k v)
  normal k (KanNe i u vs v) = KanNe i (normal k u) (normal k vs) (normal k v)
  normal k (KanUElem us u) = kanUElem (normal k us) (normal k u)
  normal k (UnKan hisos u) = UnKan (normal k hisos) (normal k u)

  normal k (VId a u0 u1) = VId a' u0' u1'
    where (a',u0',u1') = normal k (a,u0,u1)

  normal k (Path i u) = Path i (normal k u)
  normal k (VSigma u v) = VSigma (normal k u) (normal k v)
  normal k (VSPair u v) = VSPair (normal k u) (normal k v)
  normal k (VCon n us) = VCon n (normal k us)

  normal k (Glue hisos u) = glue (normal k hisos) (normal k u)
  normal k (UnGlue hisos u) = UnGlue (normal k hisos) (normal k u)
  normal k (GlueElem us u) = glueElem (normal k us) u
  normal k (GlueLine shape u phi) = glueLine shape (normal k u) phi
  normal k (GlueLineElem shape u phi) = glueLineElem shape (normal k u) phi

  normal k (VExt phi u v w) = VExt phi u' v' w'
    where (u',v',w') = normal k (u,v,w)

  normal k (VInh u)  = VInh (normal k u)
  normal k (VInc u)  = VInc (normal k u)
  normal k (VSquash phi u v) = VSquash phi (normal k u) (normal k v)

  normal _ VCircle = VCircle
  normal _ VBase   = VBase
  normal _ (VLoop phi) = VLoop phi

  normal k (VApp u v) = app (normal k u) (normal k v)
  normal k (VAppFormula u phi) = normal k u @@ phi
  normal k (VFst u) = fstSVal (normal k u)
  normal k (VSnd u) = sndSVal (normal k u)
  normal k (VSplit u v) = VSplit (normal k u) (normal k v)

  normal k (VHSplit u v) = VHSplit (normal k u) (normal k v)
  normal k (VPCon n us phi u0 u1) =
    VPCon n (normal k us) phi (normal k u0) (normal k u1)

  normal k (VCircleRec u v w x) = VCircleRec u' v' w' x'
    where (u',v',w',x') = normal k (u,v,w,x)

  normal k (VInhRec b f h u) = VInhRec b' f' h' u'
    where (b',f',h',u') = normal k (b,f,h,u)

  normal k u = u

instance Normal a => Normal (Map k a) where
  normal k us = Map.map (normal k) us

instance (Normal a,Normal b) => Normal (a,b) where
  normal k (u,v) = (normal k u,normal k v)

instance (Normal a,Normal b,Normal c) => Normal (a,b,c) where
  normal k (u,v,w) = (normal k u,normal k v,normal k w)

instance (Normal a,Normal b,Normal c,Normal d) => Normal (a,b,c,d) where
  normal k (u,v,w,x) =
    (normal k u,normal k v,normal k w, normal k x)

instance Normal a => Normal [a] where
  normal k us = map (normal k) us

instance Normal Hiso where
  normal k (Hiso a b f g s t) = Hiso a' b' f' g' s' t'
    where [a',b',f',g',s',t'] = normal k [a,b,f,g,s,t]
