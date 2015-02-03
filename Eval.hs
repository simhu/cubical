{-# Language CPP #-}
module Eval ( eval
            , evals
            , app
            , appFormula
--            , normal
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

look :: [Name] -> Ident -> Env -> (Binder, Val)
look is x (Pair rho (n@(y,l),u))
  | x == y    = (n, u)
  | otherwise = look is x rho
look is x r@(PDef es r1) = case lookupIdent x es of
  Just (y,t)  -> (y,eval is r t)
  Nothing     -> look is x r1
look _ x Empty = error ("look:" <+> x <+> "not found")

eval :: [Name] -> Env -> Ter -> Val
eval is e v = case v of
  U                  -> VU
  pn@(PN (Undef _))  -> Ter pn (e,id)
  PN pn              -> evalAppPN is e pn []
  App r s            -> case unApps (App r s) of
    (PN pn,us) -> evalAppPN is e pn us
    _          -> app is (eval is e r) (eval is e s)
  Var i              -> snd $ look is i e
  Pi a b             -> VPi (eval is e a) (eval is e b)
  t@Lam{}            -> Ter t (e,id) -- stop at lambdas
  Where t decls      -> eval is (PDef (declDefs decls) e) t
  Sigma a b          -> VSigma (eval is e a) (eval is e b)
  SPair a b          -> VSPair (eval is e a) (eval is e b)
  Fst a              -> fstSVal $ eval is e a
  Snd a              -> sndSVal $ eval is e a
  Sum pr ntss        -> Ter (Sum pr ntss) (e,id)
  Con name ts        -> VCon name $ map (eval is e) ts
  Split pr alts      -> Ter (Split pr alts) (e,id)
  t@HSum{}           -> Ter t (e,id)
  PCon n ts ns t0 t1 -> 
    let i   = gensym is
        -- TODO: lambda abstract or not?
        -- u0 = eval e (mkLams ns t0)
        -- u1 = eval e (mkLams ns t1)

        -- The code below should be correct, but because of the other bug, we
        -- leave the incorrect thing for now
        us  = map (eval is e) ts
        upe = upds e (zip (map noLoc ns) us)
        u0  = eval is upe t0
        u1  = eval is upe t1
    in Path i $ VPCon n us (Atom i) u0 u1
  t@HSplit{}         -> Ter t (e,id)

evals :: [Name] -> Env -> [(Binder,Ter)] -> [(Binder,Val)]
evals is env = map (second (eval is env))

pathCon :: Ident -> [Val] -> Formula -> Val -> Val -> Val
pathCon n vs (Dir Zero) u _ = u -- apps u vs  -- Should be [u]
pathCon n vs (Dir One)  _ v = v -- apps v vs  -- Should be [u]
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
  support v = case v of
    VU                     -> []
    Ter _ (e,f)                -> support (mapEnv f e)
    VPi v1 v2              -> support [v1,v2]
    Kan i a ts u           -> i `delete` support (a,ts,u)
    KanNe i a ts u         -> i `delete` support (a,ts,u)
    KanUElem ts u          -> support (ts,u)
    UnKan ts u             -> support (ts,u)
    VId a v0 v1            -> support [a,v0,v1]
    Path i v               -> i `delete` support v
    VSigma u v             -> support (u,v)
    VSPair u v             -> support (u,v)
    VFst u                 -> support u
    VSnd u                 -> support u
    VCon _ vs              -> support vs
    VVar _                 -> []
    VApp u v               -> support (u, v)
    VAppFormula u phi      -> support (u, phi)
    VSplit u v             -> support (u, v)
    Glue ts u              -> support (ts, u)
    UnGlue ts u            -> support (ts, u)
    GlueElem ts u          -> support (ts, u)
    HisoProj _ e           -> support e
    GlueLine t phi psi     -> support (t,phi,psi)
    GlueLineElem t phi psi -> support (t,phi,psi)
    VExt phi f g p         -> support (phi,f,g,p)
    VPCon _ vs phi u v     -> support (vs,phi,u,v)
    VHSplit u v            -> support (u,v)
    UnGlueNe u v           -> support (u,v)
    VLam _ u               -> support u

  occurs x w = case w of
    VU                     -> False
    Ter _ (e,f)                -> occurs x (mapEnv f e)
    VPi v1 v2              -> occurs x [v1,v2]
    Kan i a ts u           -> if x == i then False else occurs x (a,ts,u)
    KanNe i a ts u         -> if x == i then False else occurs x (a,ts,u)
    KanUElem ts u          -> occurs x (ts,u)
    UnKan ts u             -> occurs x (ts,u)
    VId a v0 v1            -> occurs x [a,v0,v1]
    Path i v               -> if x == i then False else occurs x v
    VSigma u v             -> occurs x (u,v)
    VSPair u v             -> occurs x (u,v)
    VFst u                 -> occurs x u
    VSnd u                 -> occurs x u
    VCon _ vs              -> occurs x vs
    VVar _                 -> False
    VApp u v               -> occurs x (u, v)
    VAppFormula u phi      -> occurs x (u, phi)
    VSplit u v             -> occurs x (u, v)
    Glue ts u              -> occurs x (ts, u)
    UnGlue ts u            -> occurs x (ts, u)
    GlueElem ts u          -> occurs x (ts, u)
    HisoProj _ e           -> occurs x e
    GlueLine t phi psi     -> occurs x (t,phi,psi)
    GlueLineElem t phi psi -> occurs x (t,phi,psi)
    VExt phi f g p         -> occurs x (phi,f,g,p)
    VPCon _ vs phi u v     -> occurs x (vs,phi,u,v)
    VHSplit u v            -> occurs x (u,v)
    UnGlueNe u v           -> occurs x (u,v)
    VLam _ u               -> occurs x u

  act is u (i, phi) =
    let acti :: Nominal a => a -> a
        acti u = act is u (i, phi)
        fv     = support phi
        fvis   = fv ++ is
        k      = gensym $ i:fvis
        ar :: Nominal a => Name -> a -> a
        ar j u = act (k:is) (u `swap` (j,k)) (i,phi)
    in case u of
         VU                     -> VU
         Ter t (e,f) -> Ter t (e,acti . f)
         -- Ter t e                -> Ter t (acti e)
         VPi a f                -> VPi (acti a) (acti f)
         -- TODO: add k to be on the safe side?
         Kan j a ts v           -> comp (k:fvis) Pos k (ar j a) (ar j ts) (ar j v)
         -- TODO: Check that act on neutral is neutral
         KanNe j a ts v         -> comp (k:fvis) Pos k (ar j a) (ar j ts) (ar j v)
         KanUElem ts u          -> kanUElem fvis (acti ts) (acti u)
         UnKan ts u             -> UnKan (acti ts) (acti u)
         VId a u v              -> VId (acti a) (acti u) (acti v)
         Path j v               -> Path k (ar j v)
         VSigma a f             -> VSigma (acti a) (acti f)
         VSPair u v             -> VSPair (acti u) (acti v)
         VFst u                 -> VFst (acti u)
         VSnd u                 -> VSnd (acti u)
         VCon c vs              -> VCon c (acti vs)
         VVar x                 -> VVar x
         VAppFormula u psi      -> appFormula fvis (acti u) (acti psi)
         VApp u v               -> app fvis (acti u) (acti v)
         VSplit u v             -> app fvis (acti u) (acti v)
         Glue ts u              -> glue (acti ts) (acti u)
         UnGlue ts u            -> UnGlue (acti ts) (acti u)
         GlueElem ts u          -> glueElem (acti ts) (acti u)
         HisoProj n e           -> HisoProj n (acti e)
         GlueLine t phi psi     -> glueLine fvis (acti t) (acti phi) (acti psi)
         GlueLineElem t phi psi -> glueLineElem fvis (acti t) (acti phi) (acti psi)
         VExt psi f g p         -> vext (acti psi) (acti f) (acti g) (acti p)
         VPCon n vs phi u v     -> pathCon n (acti vs) (acti phi) (acti u) (acti v)
         VHSplit u v            -> app fvis (acti u) (acti v)
         UnGlueNe u v           -> app fvis (acti u) (acti v)

  -- This increases efficiency as it won't trigger computation.
  swap u ij =
    let sw :: Nominal a => a -> a
        sw u = swap u ij
    in case u of
         VU                     -> VU
         Ter t (e,f) -> Ter t (e,sw . f) 
         -- Ter t e                -> Ter t (sw e)
         VPi a f                -> VPi (sw a) (sw f)
         Kan k a ts v           -> Kan (swapName k ij) (sw a) (sw ts) (sw v)
         KanNe k a ts v         -> KanNe (swapName k ij) (sw a) (sw ts) (sw v)
         KanUElem ts u          -> KanUElem (sw ts) (sw u)
         UnKan ts u             -> UnKan (sw ts) (sw u)
         VId a u v              -> VId (sw a) (sw u) (sw v)
         Path k v               -> Path (swapName k ij) (sw v)
         VSigma a f             -> VSigma (sw a) (sw f)
         VSPair u v             -> VSPair (sw u) (sw v)
         VFst u                 -> VFst (sw u)
         VSnd u                 -> VSnd (sw u)
         VCon c vs              -> VCon c (sw vs)
         VVar x                 -> VVar x
         VAppFormula u psi      -> VAppFormula (sw u) (sw psi)
         VApp u v               -> VApp (sw u) (sw v)
         VSplit u v             -> VSplit (sw u) (sw v)
         Glue ts u              -> Glue (sw ts) (sw u)
         UnGlue ts u            -> UnGlue (sw ts) (sw u)
         GlueElem ts u          -> GlueElem (sw ts) (sw u)
         HisoProj n e           -> HisoProj n (sw e)
         GlueLine t phi psi     -> GlueLine (sw t) (sw phi) (sw psi)
         GlueLineElem t phi psi -> GlueLineElem (sw t) (sw phi) (sw psi)
         VExt psi f g p         -> VExt (sw psi) (sw f) (sw g) (sw p)
         VPCon n vs phi u v     -> pathCon n (sw vs) (sw phi) (sw u) (sw v)
         VHSplit u v            -> VHSplit (sw u) (sw v)
         UnGlueNe u v           -> UnGlueNe (sw u) (sw v)

instance Nominal Hiso where
  support (Hiso a b f g s t)     = support (a,b,f,g,s,t)
  occurs x (Hiso a b f g s t)    = occurs x (a,b,f,g,s,t)
  
  act is (Hiso a b f g s t) iphi = Hiso a' b' f' g' s' t'
    where (a',b',f',g',s',t') = act is (a,b,f,g,s,t) iphi

  swap (Hiso a b f g s t) ij     = Hiso a' b' f' g' s' t'
    where (a',b',f',g',s',t') = swap (a,b,f,g,s,t) ij

instance Nominal Env where
  support Empty          = []
  support (Pair e (_,v)) = support (e,v)
  support (PDef _ e)     = support e

  occurs x e = case e of
    Empty        -> False
    Pair e (_,v) -> occurs x (e,v)
    PDef _ e     -> occurs x e

  act is e iphi  = mapEnv (\u -> act is u iphi) e

  swap e ij = mapEnv (`swap` ij) e

-- Glueing
glue :: System Hiso -> Val -> Val
glue hisos b | Map.null hisos         = b
glue hisos b | eps `Map.member` hisos = hisoA (hisos ! eps)
glue hisos b                          = Glue hisos b

glueElem :: System Val -> Val -> Val
glueElem us v | Map.null us         = v
glueElem us v | eps `Map.member` us = us ! eps
glueElem us v                       = GlueElem us v

-- TO CHECK: this is confluent
glueLine :: [Name] -> Val -> Formula -> Formula -> Val
glueLine is t _ (Dir Zero)  = t
glueLine is t (Dir _) _     = t
glueLine is t phi (Dir One) = glue hisos t  -- TODO: support of face okay?
  where hisos = mkSystem (map (\alpha -> (alpha,idHiso (face is t alpha)))
                              (invFormula phi Zero))
glueLine is t phi psi       = GlueLine t phi psi

idHiso :: Val -> Hiso
idHiso a = Hiso a a idV idV refl refl
  where idV  = Ter (Lam (noLoc "x") (Var "x")) (Empty,id)
        refl = Ter (Lam (noLoc "x") (App (App (PN Refl) (Var "y")) (Var "x")))
                   (Pair Empty ((noLoc "y"),a),id)

glueLineElem :: [Name] -> Val -> Formula -> Formula -> Val
glueLineElem _ u (Dir _) _      = u
glueLineElem _ u _ (Dir Zero)   = u
glueLineElem is u phi (Dir One) = glueElem ss u  -- TODO: support of face okay?
  where ss = mkSystem (map (\alpha -> (alpha,face is u alpha)) (invFormula phi Zero))
glueLineElem _ u phi psi        = GlueLineElem u phi psi

unGlueLine :: [Name] -> Val -> Formula -> Formula -> Val -> Val
unGlueLine is b phi psi u = case (phi,psi,u) of
 (Dir _,_,_)                            -> u
 (_,Dir Zero,_)                         -> u
 (_,Dir One,_)                          ->  -- TODO: support of face okay?
   let hisos = mkSystem (map (\alpha -> (alpha,idHiso (face is b alpha)))
                             (invFormula phi Zero))
   in app is (UnGlue hisos b) u -- TODO: support okay?
 (_,_,GlueLineElem w _ _ )              -> w
 (_,_,KanUElem _ (GlueLineElem w _ _ )) -> w
 (_,_,_)                                ->
   error ("UnGlueLine, should be GlueLineElem " <+> show u)

kanUElem :: [Name] -> System Val -> Val -> Val
kanUElem _ us v | Map.null us         = v
kanUElem _ us v | eps `Map.member` us = us ! eps
kanUElem is us (KanUElem vs w)        = KanUElem ws w
  where
    ws' = Map.mapWithKey (\alpha vAlpha -> kanUElem is (face is us alpha) vAlpha) vs
    ws  = insertsSystem (Map.toList us) ws'
kanUElem _ us v = KanUElem us v

vext :: Formula -> Val -> Val -> Val -> Val
vext (Dir Zero) f _ _ = f
vext (Dir One)  _ g _ = g
vext phi f g p        = VExt phi f g p

-- Application
app :: [Name] -> Val -> Val -> Val
app is (Ter (Lam x t) (e,f)) u                = eval is (Pair (mapEnv f e) (x,u)) t
app is kan@(Kan i b@(VPi a f) ts li0) ui1 =
  -- DT.trace "app Kan VPi" $
    let -- j   = fresh (kan,ui1)
        j   = gensym is
        (aj,fj,tsj) = (a,f,ts) `swap` (i,j)
        u   = fill (j:is) Neg j aj Map.empty ui1
        --ui0 = u `face` (j ~> 0)
        ui0 = comp (j:is) Neg j aj Map.empty ui1
    in comp (j:is) Pos j (app (j:is) fj u)
           (Map.intersectionWith (app (j:is)) tsj (border (j:is) u tsj))
           (app is li0 ui0)
app is u@(Ter (Split _ _) _) (KanUElem _ v) = app is u v
app is (Ter (Split _ nvs) (e,f)) (VCon name us) = case lookup name nvs of
  Just (xs,t)  -> eval is (upds (mapEnv f e) (zip xs us)) t
  Nothing -> error $ "app: Split with insufficient arguments; " ++
                        "missing case for " ++ name


-- TODO: is this correct even for HITs???
app is u@(Ter (HSplit _ _ hbr) _) (KanUElem _ v) = app is u v

app is (Ter (HSplit _ _ hbr) (e,f)) (VCon name us) =
  case lookup name (zip (map hBranchToLabel hbr) hbr) of
    Just (Branch _ xs t)  -> eval is (upds (mapEnv f e) (zip xs us)) t
    _ -> error ("app: HSplit with insufficient arguments;"
                <+> "missing case for " <+> name <+> show hbr)

-- cubical: app: HSplit with insufficient arguments; missing case for
--   north [Branch "base" [] z.1,HBranch "loop" [] z.2]

app is (Ter (HSplit _ _ hbr) (e,f)) (VPCon name us phi _ _) =
  case lookup name (zip (map hBranchToLabel hbr) hbr) of
    Just (HBranch _ xs t) -> appFormula is (eval is (upds (mapEnv f e) (zip xs us)) t) phi
    _ -> error ("app: HSplit with insufficient arguments;"
                <+> "missing case for " <+> name <+> show hbr)

app is u@(Ter (HSplit _ f hbr) (e,ff)) kan@(Kan i v ws w) = -- v should be corr. hsum
  let --j     = fresh (mapEnv ff e,kan)
      j     = gensym is
      wsij  = ws `swap` (i,j)
      ws'   = Map.mapWithKey (\alpha -> app (j:is) (face (j:is) u alpha)) wsij
      w'    = app is u w  -- app (u `face` (i ~> 0)) w
      ffill = app (j:is) (eval (j:is) (mapEnv ff e) f) (fill (j:is) Pos j (v `swap` (i,j)) wsij w)
  in comp (j:is) Pos j ffill ws' w'

app is g@(UnGlue hisos b) w
    | Map.null hisos         = w
    | eps `Map.member` hisos = app is (hisoF (hisos ! eps)) w
    | otherwise              = case w of
       GlueElem us v   -> v
       KanUElem _ v    -> app is g v
       _ | isNeutral w -> UnGlueNe g w
       _               -> error $ "app (Unglue):" <+> show w
                                  <+> "should be neutral!"

app is g@(UnKan hisos b) w
    | Map.null hisos         = w
    | eps `Map.member` hisos = app is (hisoF (hisos ! eps)) w
    | otherwise              = kanUElem is (Map.mapWithKey (\alpha hisoAlpha ->
                                 app is (hisoF hisoAlpha) (face is w alpha))
                               hisos) w

-- TODO: recheck at least 1 more time (please decrease the counter if
-- you checked)
app is (HisoProj hisoProj e) u = -- DT.trace "app HisoProj" $
  case hisoProj of
    HisoSign sign -> comp (i:is) sign i (appFormula (i:is) e i) Map.empty u
    -- f (g y) -> y
    IsSection     ->
      let ts = Map.fromList [(i ~> 0, line Pos j (appiso Neg u)), (i ~> 1, u)]
      in  Path i $ comp (i:j:is) Pos j (appFormula (i:j:is) e (Atom i :\/: Atom j)) ts (line Neg i u)
    -- g (f x) -> x
    IsRetraction ->
      let ts = Map.fromList [(i ~> 0, u), (i ~> 1, line Neg j (appiso Pos u))]
      in Path i $
           sym (i:j:is) (comp (i:j:is) Neg j (appFormula (i:j:is) e (Atom i :/\: Atom j)) ts (line Pos i u)) i
  where i:j:_ = gensyms is
        appiso sign v = app is (HisoProj (HisoSign sign) e) v
        line sign k v = fill (i:j:is) sign k (appFormula (i:j:is) e k) Map.empty v

app _ u@(Ter (Split _ _) _) v
  | isNeutral v = VSplit u v -- v should be neutral
  | otherwise   = error $ "app: (VSplit) " ++ show v ++ " is not neutral"
app _ u@(Ter (HSplit _ _ _) _) v
  | isNeutral v = VHSplit u v -- v should be neutral
  | otherwise   = error $ "app: (VHSplit) " ++ show v ++ " is not neutral"
app is u@(VExt phi f g p) v = appFormula is (app is p v) phi
app _ r s
 | isNeutral r = VApp r s -- r should be neutral
 | otherwise   = error $ "app: (VApp) " ++ show r ++ " is not neutral"

apps :: [Name] -> Val -> [Val] -> Val
apps is = foldl (app is)

-- (@@) :: ToFormula a => Val -> a -> Val
-- (Path i u) @@ phi = u `act` (i, toFormula phi)
-- (KanUElem _ u) @@ phi = u @@ phi
-- v @@ phi          = VAppFormula v (toFormula phi)

appFormula :: ToFormula a => [Name] -> Val -> a -> Val
appFormula is (Path i u) phi     = act is u (i, toFormula phi)
appFormula is (KanUElem _ u) phi = appFormula is u phi
appFormula _  v          phi     = VAppFormula v (toFormula phi)

-- Grad Lemma, takes a iso an L-system ts a value v s.t. sigma us = border v
-- outputs u s.t. border u = us and an L-path between v and sigma u
-- an theta is a L path if L-border theta is constant
gradLemma :: [Name] -> Hiso -> System Val -> Val -> (Val, Val)
gradLemma is hiso@(Hiso a b f g s t) us v = trace "gradLemma" $ (u, Path i theta'')
  where i:j:_   = gensyms is
        is'     = i:j:is
        us'     = Map.mapWithKey (\alpha uAlpha ->
                                   appFormula is' (app is' (face is' t alpha) uAlpha) i) us
        theta   = fill is' Pos i a us' (app is' g v)
        --u       = theta `face` (i ~> 1)
        u       = comp is' Pos i a us' (app is' g v)
        ws      = insertSystem (i ~> 0) (app is' g v) $
                  insertSystem (i ~> 1) (appFormula is' (app is' t u) j) $
                  Map.mapWithKey
                    (\alpha uAlpha ->
                      appFormula is' (app is' (face is' t alpha) uAlpha) (Atom i :/\: Atom j)) us
        theta'  = comp is' Neg j a ws theta
        xs      = insertSystem (i ~> 0) (appFormula is' (app is' s v) j) $
                  insertSystem (i ~> 1) (appFormula is' (app is' s (app is' f u)) j) $
                  Map.mapWithKey
                    (\alpha uAlpha ->
                      appFormula is' (app is' (face is' s alpha) (app is' (face is' f alpha) uAlpha)) j) us
        theta'' = comp is' Pos j b xs (app is' f theta')


-- any equality defines an equivalence Lemma 4.2
eqLemma :: [Name] -> Val -> System Val -> Val -> (Val, Val)
eqLemma is e ts a = trace "eqLemma" $ (t, Path j theta'')
  where i:j:_   = gensyms is
        is'     = i:j:is
        ei      = appFormula is' e i
        vs      = Map.mapWithKey (\alpha uAlpha ->
                    fill is' Pos i (face is' ei alpha) Map.empty uAlpha) ts
        theta   = fill is' Neg i ei vs a
        t       = comp is' Neg i ei vs a
        --t       = theta `face` (i ~> 0)
        theta'  = fill is' Pos i ei Map.empty t
        ws      = insertSystem (j ~> 1) theta' $
                  insertSystem (j ~> 0) theta $ vs
        theta'' = comp is' Pos i ei ws t

eqHiso :: [Name] -> Val -> Hiso
eqHiso is e = Hiso (appFormula is e Zero) (appFormula is e One)
                   (HisoProj (HisoSign Pos) e) (HisoProj (HisoSign Neg) e)
                   (HisoProj IsSection e) (HisoProj IsRetraction e)

-- Apply a primitive notion
evalAppPN :: [Name] -> Env -> PN -> [Ter] -> Val
evalAppPN is e pn ts
  | length ts < arity pn =
      -- Eta expand primitive notions
      let r       = arity pn - length ts
          binders = map (\n -> '_' : show n) [1..r]
          vars    = map Var binders
      in Ter (mkLams binders $ mkApps (PN pn) (ts ++ vars)) (e,id)
  | otherwise =
      let (args,rest) = splitAt (arity pn) ts
          vas = map (eval is e) args
          p   = evalPN pn vas
          r   = map (eval is e) rest
      in apps ([i,j,k] ++ is) p r -- TODO: ugly magic number; calculate vars in evalPN
   where
     i:j:k:_  = gensyms is     

     -- Evaluate primitive notions
     evalPN :: PN -> [Val] -> Val
     evalPN pn vs = case (pn,vs) of
       (Id,[a,a0,a1])        -> VId (Path i a) a0 a1
       (IdP,[_,_,p,a0,a1])   -> VId p a0 a1
       (Refl,[_,a])          -> Path i a
       (Sym,[_,_,_,p])       -> Path i $ appFormula (i:is) p (NegAtom i)
       (TransU,[_,_,p,t])    -> comp (i:is) Pos i (appFormula (i:is) p i) Map.empty t
       (TransInvU,[_,_,p,t]) -> comp (i:is) Neg i (appFormula (i:is) p i) Map.empty t
       (CSingl,[_,_,_,p])    -> Path i $ VSPair q (Path j (connect (i:j:is) q (i,j)))
         where q = appFormula (i:is) p i
       (Ext,[_,_,f,g,p])     -> Path i $ VExt (Atom i) f g p
       (IsoId,[a,b,f,g,s,t]) ->
         Path i $ Glue (mkSystem [(i ~> 0, Hiso a b f g s t)]) b
       (IsoIdRef,[a])                -> Path j $ Path i $ GlueLine a (Atom i) (Atom j)
       (MapOnPath,[_,_,f,_,_,p])     -> Path i $ app (i:is) f (appFormula (i:is) p i)
       (MapOnPathD,[_,_,f,_,_,p])    -> Path i $ app (i:is) f (appFormula (i:is) p i)
       (AppOnPath,[_,_,_,_,_,_,p,q]) ->
         Path i $ app (i:is) (appFormula (i:is) p i) (appFormula (i:is) q i)
       (MapOnPathS,[_,_,_,f,_,_,p,_,_,q]) ->
         Path i $ app (i:is) (app (i:is) f (appFormula (i:is) p i)) (appFormula (i:is) q i)
       (LemSimpl,[v,a,_,_,p,q,q',s]) -> Path j $ Path k $ comp is' Pos i v ss a
         where ss = mkSystem [(j ~> 0,fill is' Pos k v (mkSystem [(i ~> 0,a),
                                                                  (i ~> 1,appFormula is' q j)])
                                                       (appFormula is' p i)),
                              (j ~> 1,fill is' Pos k v (mkSystem [(i ~> 0,a),
                                                                  (i ~> 1,appFormula is' q' j)])
                                                       (appFormula is' p i)),
                              (k ~> 0,appFormula is' p i),
                              (k ~> 1,appFormula is' (appFormula is' s j) i)]
               is' = i:j:k:is
       (Transpose,[_,_,_,_,_,_,_,_,_,x]) ->
         Path j $ Path i $ (appFormula (i:j:is) (appFormula (i:is) x i) j)
       (IdSElim,[_,_,p,u,_,x]) ->
         Path j $ comp (i:j:is) Pos i (appFormula (i:j:is) p i) ss u
         where ss = mkSystem [(j ~> 1, appFormula (i:j:is) x i)]
       (u,_) -> error ("evalPN " ++ show u)

comps :: [Name] -> Name -> [(Binder,Ter)] -> Env -> [(System Val,Val)] -> [Val]
comps is i []         _ []            = []
comps is i ((x,a):as) e ((ts,u):tsus) =
  let v  = fill (i:is) Pos i (eval (i:is) e a) ts u
      -- vi1 = v `face` (i ~> 1)
      vi1 = comp is Pos i (eval (i:is) e a) ts u
      vs  = comps is i as (Pair e (x,v)) tsus
  in vi1 : vs
comps _ _ _ _ _ = error "comps: different lengths of types and values"

fills :: [Name] -> Name -> [(Binder,Ter)] -> Env -> [(System Val,Val)] -> [Val]
fills _  i []         _ []            = []
fills is i ((x,a):as) e ((ts,u):tsus) =
  let v  = fill is Pos i (eval (i:is) e a) ts u
      -- vi0 = v `face` (i ~> 1)
      vs  = fills is i as (Pair e (x,v)) tsus
  in v : vs
fills _ _ _ _ _ = error "fills: different lengths of types and values"

isNeutral :: Val -> Bool
isNeutral (VVar _)               = True
isNeutral (VApp u _)             = isNeutral u
isNeutral (VAppFormula u _)      = isNeutral u
isNeutral (VFst v)               = isNeutral v
isNeutral (VSnd v)               = isNeutral v
isNeutral (VSplit _ v)           = isNeutral v
isNeutral (Kan _ a ts u)         = -- TODO: Maybe remove?
  isNeutral a || isNeutralSystem ts || isNeutral u
isNeutral (KanUElem _ u)         = isNeutral u  -- TODO: check this!
isNeutral (KanNe _ _ _ _)        = True
isNeutral (VHSplit _ v)          = isNeutral v
isNeutral (UnGlueNe _ v)         = isNeutral v
isNeutral (Ter (PN (Undef _)) _) = True
isNeutral _                      = False

isNeutralSystem :: System Val -> Bool
isNeutralSystem = any isNeutral . Map.elems

fill :: [Name] -> Sign -> Name -> Val -> System Val -> Val -> Val
fill is Neg i a ts u = trace "fill Neg" $  -- i should be in is (added just to be sure)
                       sym (i:is) (fill is Pos i (sym (i:is) a i) (sym (i:is) ts i) u) i
fill is Pos i a ts u = trace "fill Pos" $
                       comp (i:j:is) Pos j (connect (i:j:is) a (i,j)) (connect (i:j:is) ts (i,j)) u
  where j = gensym (i:is)

comp :: [Name] -> Sign -> Name -> Val -> System Val -> Val -> Val
comp is sign i a ts u | i `notOccurs` (a,ts) = trace "comp cheaply regular" $ u
-- Another possible optimization:
comp is sign i a ts u | i `notOccurs` a && not (Map.null indep) =
  trace "comp filter" $ comp is sign i a ts' u
  where (ts',indep) = Map.partition (occurs i) ts
comp is Neg i a ts u = comp is Pos i (sym (i:is) a i) (sym (i:is) ts i) u

-- If 1 is a key of ts, then it means all the information is already there.
-- This is used to take (k = 0) of a comp when k \in L
comp is Pos i a ts u | eps `Map.member` ts = trace "easy case of comp" $
                                             act (i:is) (ts ! eps) (i,Dir 1)
comp is Pos i (KanUElem _ a) ts u = comp is Pos i a ts u
comp is Pos i vid@(VId a u v) ts w = Path j $ comp (i:j:is) Pos i (appFormula (i:j:is) a j)
                                                   ts' (appFormula (i:j:is) w j)
  where j   = gensym (i:is)
        ts' = insertSystem (j ~> 0) u $
              insertSystem (j ~> 1) v $
              Map.map (\u -> appFormula (i:j:is) u j) ts
comp is Pos i b@(VSigma a f) ts u = VSPair ui1 comp_u2
  where (t1s, t2s) = (Map.map fstSVal ts, Map.map sndSVal ts)
        (u1,  u2)  = (fstSVal u, sndSVal u)
        fill_u1    = fill (i:is) Pos i a t1s u1
        -- ui1        = fill_u1 `face` (i ~> 1)
        ui1        = comp is Pos i a t1s u1
        comp_u2    = comp is Pos i (app (i:is) f fill_u1) t2s u2
comp is Pos i a@VPi{} ts u   = Kan i a ts u
comp is Pos i g@(Glue hisos b) ws wi0 =
  trace ("comp Glue") $ -- \n ShapeOk: " ++ show (shape usi1 == shape hisosI1))
    glueElem usi1 vi1''
  where is'  = i:is
        unglue = UnGlue hisos b
        vs   = Map.mapWithKey
                 (\alpha wAlpha -> app is' (face is' unglue alpha) wAlpha) ws
        vi0  = app is' (face is' unglue (i ~> 0)) wi0 -- in b(i0)

        v    = fill is' Pos i b vs vi0           -- in b
        --vi1  = v `face` (i ~> 1)
        vi1  = comp is' Pos i b vs vi0           -- in b(i1)

        hisosI1 = face is' hisos (i ~> 1)
        -- (hisos', hisos'') = Map.partitionWithKey
        --                     (\alpha _ -> alpha `Map.member` hisos) hisosI1

        hisos'' = Map.filterWithKey (\alpha _ -> not (alpha `Map.member` hisos)) hisosI1

        -- set of elements in hisos independent of i
        --hisos'  = Map.filterWithKey (\alpha _ -> not (leq alpha (i ~> 1))) hisos
        hisos'  = Map.filterWithKey (\alpha _ -> i `Map.notMember` alpha) hisos

        us'    = Map.mapWithKey (\gamma (Hiso aGamma _ _ _ _ _) ->
                  fill is' Pos i aGamma (face is' ws gamma) (face is' wi0 gamma))
                hisos'
        usi1'  = Map.mapWithKey (\gamma (Hiso aGamma _ _ _ _ _) ->
                  comp is' Pos i aGamma (face is' ws gamma) (face is' wi0 gamma))
                hisos'
        --usi1'  = Map.map (\u -> u `face` (i ~> 1)) us'

        ls'    = Map.mapWithKey (\gamma (Hiso aGamma bGamma fGamma _ _ _) ->
                  pathComp is' i bGamma (face is' vs gamma)
                    (face is' v gamma) (app is' fGamma (us' ! gamma)))
                 hisos'

        vi1'  = compLine is' (face is' b (i ~> 1)) ls' vi1

        uls''   = Map.mapWithKey (\gamma hisoGamma@(Hiso aGamma bGamma fGamma _ _ _) ->
                     let shgamma :: System ()
                         shgamma = face is' (shape hisos' `unionSystem` shape ws) gamma
                         usgamma = Map.mapWithKey
                           (\beta _ ->
                             let delta = gamma `meet` beta
                             in if delta `leqSystem` ws
                                then proj is' ws (delta `meet` (i ~> 1))
                                else proj is' usi1' delta)
                           shgamma
                     in gradLemma is' hisoGamma usgamma (face is' vi1' gamma))
                   hisos''

        vi1''   = compLine is' (face is' b (i ~> 1)) (Map.map snd uls'') vi1'

        usi1    = Map.mapWithKey (\gamma _ ->
                    if gamma `Map.member` usi1' then usi1' ! gamma
                    else fst (uls'' ! gamma))
                  hisosI1
comp is Pos i t@(Kan j VU ejs b) ws wi0 =
    let is'   = i:j:is
        es    = Map.map (Path j . (\u -> sym is' u j)) ejs
        hisos = Map.map (eqHiso is') es
        unkan = UnKan hisos b

        vs    = Map.mapWithKey (\alpha wAlpha -> app is' (face is' unkan alpha) wAlpha) ws
        vi0   = app is' (face is' unkan (i ~> 0)) wi0 -- in b(i0)

        vi1     =  comp is' Pos i b vs vi0           -- in b(i1)

        hisosI1 = face is' hisos (i ~> 1)

        --  {(gamma, sigma gamma (i1)) | gamma elem hisos}
        hisos'' = Map.filterWithKey (\alpha _ -> not (alpha `Map.member` hisos)) hisosI1

        -- set of elements in hisos independent of i
        --hisos'  = Map.filterWithKey (\alpha _ -> not (leq alpha (i ~> 1))) hisos
        hisos'  = Map.filterWithKey (\alpha _ -> i `Map.notMember` alpha) hisos

        -- (hisos', hisos'') = Map.partitionWithKey
        --                     (\alpha _ -> alpha `Map.member` hisos) hisosI1

        usi1'    = Map.mapWithKey (\gamma (Hiso aGamma _ _ _ _ _) ->
                     comp is' Pos i aGamma (face is' ws gamma) (face is' wi0 gamma))
                   hisos'

        ls'    = Map.mapWithKey (\gamma _ ->
                   pathUniv is' i (proj is' es gamma) (face is' ws gamma) (face is' wi0 gamma))
                 hisos'

        vi1'  = compLine is' (face is' b (i ~> 1)) ls' vi1

        uls''   = Map.mapWithKey (\gamma hisoGamma@(Hiso aGamma bGamma fGamma _ _ _) ->
                     let shgamma :: System ()
                         shgamma = face is' (shape hisos' `unionSystem` shape ws) gamma
                         usgamma =
                           Map.mapWithKey
                             (\beta _ ->
                               let delta = gamma `meet` beta
                               in if delta `leqSystem` ws
                                  then proj is' ws (delta `meet` (i ~> 1))
                                  else proj is' usi1' delta)
                             shgamma
                     in eqLemma is' (proj is' es (gamma `meet` (i ~> 1)))
                          usgamma (face is' vi1' gamma)) hisos''

        vi1''   = compLine is' (face is' b (i ~> 1)) (Map.map snd uls'') vi1'

        usi1    = Map.mapWithKey (\gamma _ ->
                    if gamma `Map.member` usi1' then usi1' ! gamma
                    else fst (uls'' ! gamma))
                  hisosI1
    in trace ("comp Kan VU\n Shape Ok: " ++ show (shape usi1 == shape hisosI1)) $
       kanUElem is' usi1 vi1''
comp is Pos i (GlueLine b phi psi) us u = DT.trace "comp GlueLine" $
                                          glueLineElem is' vm phii1 psii1
  where  is'   = i:is
         phii1 = face is' phi (i ~> 1)
         psii1 = face is' psi (i ~> 1)
         phii0 = face is' phi (i ~> 0)
         psii0 = face is' psi (i ~> 0)
         bi1   = face is' b (i ~> 1)
         bi0   = face is' b (i ~> 0)
         lss   = mkSystem (map (\alpha ->
                               (alpha,(face is' phi alpha,face is' b alpha,
                                       face is' us alpha,face is' u alpha))) fs)
         ls = Map.mapWithKey (\alpha vAlpha -> auxGlueLine is' i vAlpha (face is' v alpha)) lss
         v  = comp is' Pos i b ws w
         ws = Map.mapWithKey (\alpha -> unGlueLine is' (face is' b alpha)
                                        (face is' phi alpha) (face is' psi alpha)) us
         w  = unGlueLine is' bi0 phii0 psii0 u
         vm = compLine is' (face is' b (i ~> 1)) ls v
         fs = filter (i `Map.notMember`) (invFormula psi One)
comp _ Pos i VU ts u = Kan i VU ts u
comp is Pos i v@(Ter (Sum _ _) _) tss (KanUElem _ w) = comp is Pos i v tss w
comp _ Pos i a ts u | isNeutral a || isNeutralSystem ts || isNeutral u =
  trace "comp Neutral" $ KanNe i a ts u
comp is Pos i v@(Ter (Sum _ nass) (env,f)) tss (VCon n us) = case getIdent n nass of
  Just as -> VCon n $ comps is i as (mapEnv f env) tsus
    where tsus = transposeSystemAndList (Map.map unCon tss) us
  Nothing -> error $ "comp: missing constructor in labelled sum " ++ n
-- Treat transport in hsums separately.
comp is Pos i v@(Ter (HSum _ hls) (env,f)) us u | Map.null us = case u of
  VCon c ws -> case getIdent c (map hLabelToBinderTele hls) of
    Just as -> VCon c (comps is i as (mapEnv f env) (zip (repeat Map.empty) ws))
    Nothing -> error $ "comp HSum: missing constructor in hsum" <+> c
  VPCon c ws0 phi e0 e1 -> case getIdent c (mapHLabelToBinderTele hls) of
    -- u should be independent of i, so i # phi
    Just (as, _,_) ->VPCon c ws1 phi (tr e0) (tr e1)
      where  -- The following seems correct when [phi] is a variable, but
             -- otherwise we need to do an induction on [phi]
        tr  = comp is Pos i v Map.empty
        ws1 = comps is i as (mapEnv f env) (zip (repeat Map.empty) ws0)
    Nothing -> error $ "comp HSum: missing path constructor in hsum" <+> c
  Kan j b ws w -> comp (k:i:is) Pos k vi1 ws' (transp (i ~> 1) w)
    where vi1 = face (i:is) v (i ~> 1)  -- b is vi0 and independent of j
          -- k   = gensym (support (v,u,Atom i))
          k   = gensym (i:is)
          transp alpha = comp is Pos i (face (i:is) v alpha) Map.empty
          wsjk         = ws `swap` (j,k)
          ws'          = Map.mapWithKey transp wsjk
  u | isNeutral u -> KanNe i v us u
  KanUElem _ u1 -> comp is Pos i v us u1
  u -> error $ "comp HSum:" <+> show u <+> "should be neutral"
comp is Pos i v@(Ter (HSum _ _) _) us u
  | i `notOccurs` us' = transp i v u
  | otherwise         = Kan i (vi1) us' (transp i v u)
    where vi1         = face (i:is) v (i ~> 1)
          -- j           = gensym (support (v,us,u,Atom i))
          j           = gensym (i:is)
          comp' alpha = transp j (act (i:is) (face (i:is) v alpha) (i, Atom i :\/: Atom j))
          us'         = Map.mapWithKey comp' us
          transp j w  = comp (i:j:is) Pos j w Map.empty
comp is Pos i a ts u =
  error $ "comp _: not implemented for \n a = " <+> show a <+> "\n" <+>
          "ts = " <+> show ts <+> "\n" <+> "u = " <+> parens (show u)

-- Lemma 2.1
-- assumes u and u' : A are solutions of us + (i0 -> u(i0))
-- (in the Pos case, otherwise we symmetrize)
-- The output is an L-path in A(i1) between u(i1) and u'(i1)
pathComp :: [Name] -> Name -> Val -> System Val -> (Val -> Val -> Val)
pathComp is i a us u u' = trace "pathComp"
                       Path j $ comp (i:j:is) Pos i a us' (face (i:j:is) u (i ~> 0))
  where --j   = fresh (Atom i, a, us, u, u')
        j   = gensym (i:is)
        us' = insertsSystem [(j ~> 0, u), (j ~> 1, u')] us

-- Lemma 6.1 Computes a homotopy between the image of the composition,
-- and the composition of the image.  Given e (an equality in U), an
-- L-system us (in e0) and ui0 (in e0 (i0)) The output is an L(i1)-path in
-- e1(i1) between vi1 and sigma (i1) ui1 where
--   sigma = HisoProj (ProjSign Pos) e
--   ui1 = comp Pos i (e 0) us ui0
--   vi1 = comp Pos i (e 1) (sigma us) (sigma(i0) ui0)
-- Moreover, if e is constant, so is the output.
pathUniv :: [Name] -> Name -> Val -> System Val -> Val -> Val
pathUniv is i e us ui0 = Path k xi1
  where j:k:_ = gensyms (i:is)
        is'   = i:j:k:is
        -- f     = HisoProj (HisoSign Pos) e
        ej    = appFormula is' e j
        ui1   = comp is' Pos i (appFormula is' e Zero) us ui0
        ws    = Map.mapWithKey (\alpha uAlpha ->
                  fill is' Pos j (face is' ej alpha) Map.empty uAlpha) us
        wi0   = fill is' Pos j (face is' ej (i ~> 0)) Map.empty ui0
        wi1   = comp is' Pos i ej ws wi0
        wi1'  = fill is' Pos j (face is' ej (i ~> 1)) Map.empty ui1
        xi1   = comp is' Pos j (face is' ej (i ~> 1))
                  (insertsSystem [(k ~> 1, wi1'), (k ~> 0, wi1)] Map.empty) ui1

-- Lemma 2.2
-- takes a type A, an L-system of lines ls and a value u
-- s.t. ls alpha @@ 0 = u alpha
-- and returns u' s.t. ls alpha @@ 1 = u' alpha
compLine :: [Name] -> Val -> System Val -> Val -> Val
compLine is a ls u = comp (i:is) Pos i a (Map.map (\v -> appFormula (i:is) v i) ls) u
  -- TODO also check pathComp; are the dirs correct?
  where i = gensym is

-- the same but now computing the line
fillLine :: [Name] -> Val -> System Val -> Val -> Val
fillLine is a ls u = trace ("compLine \n a=" ++ show a ++ "\n u = " ++ show u)
  Path i (fill (i:is) Pos i a (Map.map (\v -> appFormula (i:is) v i) ls) u)
  where i = gensym is

-- auxiliary function needed for composition for GlueLine
auxGlueLine :: [Name] -> Name -> (Formula,Val,System Val,Val) -> Val -> Val
auxGlueLine is i (Dir _,b,ws,wi0) vi1 = Path j vi1
  where j = gensym is
auxGlueLine is i (phi,b,ws,wi0) vi1   = fillLine is' (face is' b (i ~> 1)) ls' vi1
  where is'    = i:is
        unglue = UnGlue hisos b
        hisos  = mkSystem (map (\ alpha -> (alpha,idHiso (face is' b alpha)))
                               (invFormula phi Zero)) -- TODO: correct support?
        vs     = Map.mapWithKey (\alpha -> app is' (face is' unglue alpha)) ws
        vi0    = app is' (face is' unglue (i ~> 0)) wi0 -- in b(i0)
        v      = fill is' Pos i b vs vi0           -- in b
        -- set of elements in hisos independent of i
        hisos' = Map.filterWithKey (\alpha _ -> i `Map.notMember` alpha) hisos
        us'    = Map.mapWithKey (\gamma (Hiso aGamma _ _ _ _ _) ->
                  fill is' Pos i aGamma (face is' ws gamma) (face is' wi0 gamma))
                 hisos'
        ls'    = Map.mapWithKey (\gamma (Hiso aGamma _ _ _ _ _) ->
                  pathComp is' i aGamma (face is' vs gamma) (face is' v gamma) (us' ! gamma))
                 hisos'

-------------------------------------------------------------------------------
-- | Conversion

class Convertible a where
  conv   :: [Name] -> Int -> a -> a -> Bool

instance Convertible Val where
  conv is _ u v | u == v = True
  conv is k VU VU                                  = True
  conv is k w@(Ter (Lam x u) (e,f)) w'@(Ter (Lam x' u') (e',f')) =
    let v = mkVar k
    in trace ("conv is Lam Lam \n w = " ++ show w ++ " \n w' = " ++ show w')
     conv is (k+1) (eval is (Pair (mapEnv f e) (x,v)) u) (eval is (Pair (mapEnv f' e') (x',v)) u')
  conv is k w@(Ter (Lam x u) (e,f)) u' =
    let v = mkVar k
    in trace ("conv Lam u' \n w = " ++ show w ++ " \n u' = " ++ show u')
        conv is (k+1) (eval is (Pair (mapEnv f e) (x,v)) u) (app is u' v)
  conv is k u' w'@(Ter (Lam x u) (e,f)) =
    let v = mkVar k
    in trace ("conv u' Lam \n u' = " ++ show u' ++ " \n w' = " ++ show w')
       conv is (k+1) (app is u' v) (eval is (Pair (mapEnv f e) (x,v)) u)
  conv is k (Ter (Split p _) (e,f)) (Ter (Split p' _) (e',f')) =
    p == p' && conv is k (mapEnv f e) (mapEnv f' e')
  conv is k (Ter (Sum p _) (e,f))   (Ter (Sum p' _) (e',f')) =
    p == p' && conv is k (mapEnv f e) (mapEnv f' e')
  conv is k (Ter (PN (Undef p)) (e,f)) (Ter (PN (Undef p')) (e',f')) =
    p == p' && conv is k (mapEnv f e) (mapEnv f' e')
  conv is k (Ter (HSum p _) (e,f))   (Ter (HSum p' _) (e',f')) =
    p == p' && conv is k (mapEnv f e) (mapEnv f' e')
  conv is k (Ter (HSplit p _ _) (e,f)) (Ter (HSplit p' _ _) (e',f')) =
    p == p' && conv is k (mapEnv f e) (mapEnv f' e')
  conv is k (VPCon c us phi _ _) (VPCon c' us' phi' _ _) =
    -- TODO: can we ignore the faces?
    c == c' && conv is k (us,phi) (us',phi')
  conv is k (VPi u v) (VPi u' v') =
    let w = mkVar k
    in conv is k u u' && conv is (k+1) (app is v w) (app is v' w)

  conv is k (VId a u v) (VId a' u' v') = conv is k (a,u,v) (a',u',v')
  conv is k v@(Path i u) v'@(Path i' u')    =
    trace "conv Path Path" conv (j:is) k (u `swap` (i,j)) (u' `swap` (i',j))
    where j = gensym (i:i':is)
  conv is k v@(Path i u) p'              = trace "conv is Path p" $
                                      conv (j:is) k (u `swap` (i,j)) (appFormula (j:is) p' j)
    where j = gensym (i:is)
  conv is k p v'@(Path i' u')             = trace "conv p Path" $
                                      conv (j:is) k (appFormula (j:is) p j) (u' `swap` (i',j))
    where j = gensym (i':is)

  conv is k (VSigma u v) (VSigma u' v') = conv is k u u' && conv is (k+1) (app is v w) (app is v' w)
    where w = mkVar k
  conv is k (VFst u) (VFst u')              = conv is k u u'
  conv is k (VSnd u) (VSnd u')              = conv is k u u'
  conv is k (VSPair u v)   (VSPair u' v')   = conv is k (u,v) (u',v')
  conv is k (VSPair u v)   w                =
    conv is k u (fstSVal w) && conv is k v (sndSVal w)
  conv is k w              (VSPair u v)     =
    conv is k (fstSVal w) u && conv is k (sndSVal w) v

  conv is k (VCon c us) (VCon c' us') = c == c' && conv is k us us'

  conv is k (Kan i a ts u) v' | isIndep is k i (a,ts) = trace "conv Kan regular"
    conv is k u v'
  conv is k v' (Kan i a ts u) | isIndep is k i (a,ts) = trace "conv Kan regular"
    conv is k v' u
  conv is k v@(Kan i a ts u) v'@(Kan i' a' ts' u') = trace "conv Kan" $
     let j    = gensym is
         tsj  = ts  `swap` (i,j)
         tsj' = ts' `swap` (i',j)
     in
     and [ conv (j:is) k (a `swap` (i,j)) (a' `swap` (i',j))
         , Map.keysSet tsj == Map.keysSet tsj'
         , and $ Map.elems $ Map.intersectionWith (conv (j:is) k) tsj tsj'
         , conv (j:is) k (u `swap` (i,j)) (u' `swap` (i',j))]

  conv is k (KanNe i a ts u) v' | isIndep is k i (a,ts) = trace "conv KanNe regular"
    conv is k u v'
  conv is k v' (KanNe i a ts u) | isIndep is k i (a,ts) = trace "conv KanNe regular"
    conv is k v' u
  conv is k v@(KanNe i a ts u) v'@(KanNe i' a' ts' u') =
     trace ("conv KanNe" ++ "\n   v = " ++ show v ++ "\n    v' = " ++ show v')  $
     let j    = gensym is
         tsj  = ts  `swap` (i,j)
         tsj' = ts' `swap` (i',j)
     in
     and [ conv (j:is) k (a `swap` (i,j)) (a' `swap` (i',j))
         , Map.keysSet tsj == Map.keysSet tsj'
         , and $ Map.elems $ Map.intersectionWith (conv (j:is) k) tsj tsj'
         , conv (j:is) k (u `swap` (i,j)) (u' `swap` (i',j))]


  conv is k (Glue hisos v) (Glue hisos' v') = conv is k hisos hisos' && conv is k v v'

  conv is k (KanUElem us u) v'@(KanUElem us' u') =
    conv is k u u' && conv is k us (border is v' us)
  conv is k (KanUElem us u) v'  = conv is k u v'
  conv is k v (KanUElem us' u') = conv is k v u'

  conv is k (GlueElem us u) (GlueElem us' u') = conv is k us us' && conv is k u u'

  conv is k (GlueLine ts u phi) (GlueLine ts' u' phi') =
    conv is k (ts,u,phi) (ts',u',phi')
  conv is k (GlueLineElem ts u phi) (GlueLineElem ts' u' phi') =
    conv is k (ts,u,phi) (ts',u',phi')

  conv is k (UnKan hisos v) (UnKan hisos' v') = conv is k hisos hisos' && conv is k v v'
  conv is k u@(UnGlue hisos v) u'@(UnGlue hisos' v') = conv is k hisos hisos' && conv is k v v'

  conv is k u@(HisoProj{}) u'@(HisoProj{}) = conv is (k+1) (app is u w) (app is u' w)
       where w = mkVar k

  conv is k (VExt phi f g p) (VExt phi' f' g' p') =
    conv is k (phi,f,g,p) (phi',f',g',p')

  conv is k u@(VExt phi f g p) u' = conv is (k+1) (app is u w) (app is u' w)
    where w = mkVar k

  conv is k u u'@(VExt phi f g p) = conv is (k+1) (app is u w) (app is u' w)
    where w = mkVar k

  conv is k (VVar x)  (VVar x')             = x == x'
  conv is k (VApp u v)     (VApp u' v')     = conv is k u u' && conv is k v v'
  conv is k (VAppFormula u x) (VAppFormula u' x') = conv is k u u' && (x == x')
  conv is k (VSplit u v)   (VSplit u' v')   = conv is k u u' && conv is k v v'
  conv is k (VHSplit u v)  (VHSplit u' v')  = conv is k u u' && conv is k v v'
  conv is k (UnGlueNe u v) (UnGlueNe u' v') = conv is k u u' && conv is k v v'
  conv is k _              _                = False

isIndep :: (Nominal a, Convertible a) => [Name] -> Int -> Name -> a -> Bool
isIndep is k i u = conv is k u (face is u (i ~> 0))

instance Convertible () where conv _ _ _ _ = True

instance (Convertible a, Convertible b) => Convertible (a, b) where
  conv is k (u, v) (u', v') = conv is k u u' && conv is k v v'

instance (Convertible a, Convertible b, Convertible c)
      => Convertible (a, b, c) where
  conv is k (u, v, w) (u', v', w') = and [conv is k u u', conv is k v v', conv is k w w']

instance (Convertible a,Convertible b,Convertible c,Convertible d)
      => Convertible (a,b,c,d) where
  conv is k (u,v,w,x) (u',v',w',x') = conv is k (u,v,(w,x)) (u',v',(w',x'))

instance Convertible a => Convertible [a] where
  conv is k us us' = length us == length us' && and [conv is k u u' | (u,u') <- zip us us']

instance Convertible Env where
  conv is k e e' = and $ zipWith (conv is k) (valOfEnv e) (valOfEnv e')

instance (Ord k, Convertible a) => Convertible (Map k a) where
  conv is k ts ts' =  Map.keysSet ts == Map.keysSet ts' &&
                   (and $ Map.elems $ Map.intersectionWith (conv is k) ts ts')

instance Convertible Hiso where
  conv is k (Hiso a b f g s t) (Hiso a' b' f' g' s' t') =
    conv is k [a,b,f,g,s,t] [a',b',f',g',s',t']

instance Convertible Formula where
  conv is _ phi psi = sort (invFormula phi 1) == sort (invFormula psi 1)


-- class Normal a where
--   normal :: Int -> a -> a

-- -- Does neither normalize formulas nor environments.
-- instance Normal Val where
--   normal _ VU = VU
--   normal k (Ter (Lam x u) e) = VLam name $ normal (k+1) (eval (Pair e (x,v)) u)
--     where v@(VVar name) = mkVar k
--   normal k (VPi u v) = VPi (normal k u) (normal k v)
--   normal k (Kan i u vs v) = comp Pos i (normal k u) (normal k vs) (normal k v)
--   normal k (KanNe i u vs v) = KanNe i (normal k u) (normal k vs) (normal k v)
--   normal k (KanUElem us u) = kanUElem (normal k us) (normal k u)
--   normal k (UnKan hisos u) = UnKan (normal k hisos) (normal k u)

--   normal k (VId a u0 u1) = VId a' u0' u1'
--     where (a',u0',u1') = normal k (a,u0,u1)

--   normal k (Path i u) = Path i (normal k u)
--   normal k (VSigma u v) = VSigma (normal k u) (normal k v)
--   normal k (VSPair u v) = VSPair (normal k u) (normal k v)
--   normal k (VCon n us) = VCon n (normal k us)

--   normal k (Glue hisos u) = glue (normal k hisos) (normal k u)
--   normal k (UnGlue hisos u) = UnGlue (normal k hisos) (normal k u)
--   normal k (GlueElem us u) = glueElem (normal k us) u
--   normal k (GlueLine u phi psi) = glueLine (normal k u) phi psi
--   normal k (GlueLineElem u phi psi) = glueLineElem (normal k u) phi psi

--   normal k (VExt phi u v w) = VExt phi u' v' w'
--     where (u',v',w') = normal k (u,v,w)

--   normal k (VApp u v) = app (normal k u) (normal k v)
--   normal k (VAppFormula u phi) = normal k u @@ phi
--   normal k (VFst u) = fstSVal (normal k u)
--   normal k (VSnd u) = sndSVal (normal k u)
--   normal k (VSplit u v) = VSplit (normal k u) (normal k v)

--   normal k (VHSplit u v) = VHSplit (normal k u) (normal k v)
--   normal k (VPCon n us phi u0 u1) =
--     VPCon n (normal k us) phi (normal k u0) (normal k u1)

--   normal k (UnGlueNe u v) = UnGlueNe (normal k u) (normal k v)

--   normal k u = u

-- instance Normal a => Normal (Map k a) where
--   normal k us = Map.map (normal k) us

-- instance (Normal a,Normal b) => Normal (a,b) where
--   normal k (u,v) = (normal k u,normal k v)

-- instance (Normal a,Normal b,Normal c) => Normal (a,b,c) where
--   normal k (u,v,w) = (normal k u,normal k v,normal k w)

-- instance (Normal a,Normal b,Normal c,Normal d) => Normal (a,b,c,d) where
--   normal k (u,v,w,x) =
--     (normal k u,normal k v,normal k w, normal k x)

-- instance Normal a => Normal [a] where
--   normal k us = map (normal k) us

-- instance Normal Hiso where
--   normal k (Hiso a b f g s t) = Hiso a' b' f' g' s' t'
--     where [a',b',f',g',s',t'] = normal k [a,b,f,g,s,t]
