{-# Language CPP #-}
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
trace s e = if debug then DT.trace is e else e

look :: [Name] -> Ident -> Env -> (Binder, Val)
look is x (Pair rho (n@(y,l),u))
  | x == y    = -- DT.trace ("look1 " ++ show y) $
                (n, u)
  | otherwise = look is x rho
look is x r@(PDef es r1) = case lookupIdent x es of
  Just (y,t)  -> -- DT.trace ("look3 " ++ show y) $
                 (y,eval is r t)
  Nothing     -> look is x r1
look _ x Empty = error ("look:" <+> x <+> "not found")

eval :: [Names] -> Env -> Ter -> Val
eval is e U                 = -- DT.trace "U" $
                           VU
eval is e pn@(PN (Undef _)) = -- DT.trace "undef" $
                           Ter pn (e,id)
eval is e (PN pn)           = -- DT.trace "pn" $
                           evalAppPN is e pn []
eval is e t@(App r s)       = case unApps t of
  (PN pn,us) -> -- DT.trace "appPN" $
                evalAppPN is e pn us
  _          -> -- DT.trace "app" $
                app is (eval is e r) (eval is e s)
eval is e (Var i)           = -- DT.trace ("look " ++ i) $
                           snd $ look i e
eval is e (Pi a b)          = -- DT.trace "pi" $
                           VPi (eval is e a) (eval is e b)
eval is e (Lam x t)         = -- DT.trace "lam" $
                           Ter (Lam x t) e -- stop at lambdas
eval is e (Where t decls)   = -- DT.trace "where" $
                           eval is (PDef (declDefs decls) e) t

eval is e (Sigma a b)       = -- DT.trace "sigma" $
                           VSigma (eval is e a) (eval is e b)
eval is e (SPair a b)       = -- DT.trace "spair" $
                           VSPair (eval is e a) (eval is e b)
eval is e (Fst a)           = -- DT.trace "fst" $
                           fstSVal $ eval is e a
eval is e (Snd a)           = -- DT.trace "snd" $
                           sndSVal $ eval is e a

eval is e (Sum pr ntss)     = -- DT.trace "sum" $
                           Ter (Sum pr ntss) e
eval is e (Con name ts)     = -- DT.trace "con" $
                           VCon name $ map (eval is e) ts
eval is e (Split pr alts)   = -- DT.trace "split" $
                           Ter (Split pr alts) e

eval _ e t@(HSum {})       = -- DT.trace "hsum" $
                           Ter t e
eval is e (PCon n ts ns t0 t1) = -- DT.trace "pcon"  $
  let i = gensym is
      -- TODO: lambda abstract or not?
--      u0 = eval e (mkLams ns t0)
--      u1 = eval e (mkLams ns t1)

      -- -- The code below should be correct, but because of the other bug, we
      -- -- leave the incorrect thing for now
      us = map (eval is e) ts
      upe = upds e (zip (map noLoc ns) us)
      u0 = eval is upe t0
      u1 = eval is upe t1
  in Path i $ VPCon n us (Atom i) u0 u1
eval is e t@(HSplit {})     = -- DT.trace "hsplit" $
                           Ter t e


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

  support (VVar _)                      = []
  support (VApp u v)                    = support (u, v)
  support (VAppFormula u phi)           = support (u, phi)
  support (VSplit u v)                  = support (u, v)

  support (Glue ts u)                   = support (ts, u)
  support (UnGlue ts u)                 = support (ts, u)
  support (GlueElem ts u)               = support (ts, u)
  support (HisoProj _ e)                = support e
  support (GlueLine t phi psi)          = support (t,phi,psi)
  support (GlueLineElem t phi psi)      = support (t,phi,psi)

  support (VExt phi f g p)              = support (phi,f,g,p)

  support (VPCon _ vs phi u v)          = support (vs,phi,u,v)
  support (VHSplit u v)                 = support (u,v)

  support (UnGlueNe u v)                = support (u,v)

  support (VLam _ u)                    = support u


  support (VExt x b f g p)              = support (x, [b,f,g,p])
  support (VHExt x b f g p)             = support (x, [b,f,g,p])
  support (Kan Fill a box)              = support (a, box)
  support (VFillN a box)                = support (a, box)
  support (VComN   a box@(Box _ n _ _)) = delete n (support (a, box))
  support (Kan Com a box@(Box _ n _ _)) = delete n (support (a, box))
  support (VEquivEq x a b f s t)        = support (x, [a,b,f,s,t])
           -- names x, y and values a, s, t
  support (VEquivSquare x y a s t)      = support ((x,y), [a,s,t])
  support (VPair x a v)                 = support (x, [a,v])
  support (VComp box@(Box _ n _ _))     = delete n $ support box
  support (VFill x box)                 = delete x $ support box
  support v                             = error ("support " ++ show v)


  act is u (i, phi) = -- trace ("act" <+> show u <+> parens (show i <+> "=" <+> show phi)) $
    let acti :: Nominal a => a -> a
        acti u = act is u (i, phi)
        fv     = support phi
        fvis   = fv ++ is
        k      = gensym $ i:fvis
        ar :: Nominal a => a -> a
        ar u = act (k:s) (u `swap` (j,k)) (i,phi)
    in case u of
         VU      -> VU
         Ter t e -> Ter t (acti e)
         VPi a f -> VPi (acti a) (acti f)
         Kan j a ts v -> comp Pos k (ar a) (ar ts) (ar v)
         -- TODO: Check that act on neutral is neutral
         KanNe j a ts v -> comp Pos k (ar a) (ar ts) (ar v)
         KanUElem ts u -> kanUElem (acti ts) (acti u)
         UnKan ts u    -> UnKan (acti ts) (acti u)

         VId a u v -> VId (acti a) (acti u) (acti v)
         Path j v -> Path k (ar v)

         VSigma a f -> VSigma (acti a) (acti f)
         VSPair u v -> VSPair (acti u) (acti v)
         VFst u     -> VFst (acti u)
         VSnd u     -> VSnd (acti u)

         VCon c vs  -> VCon c (acti vs)

         VVar x            -> VVar x
         VAppFormula u psi -> appFormula fvis (acti u) (acti psi)
         VApp u v          -> app fvis (acti u) (acti v)
         VSplit u v        -> app fvis (acti u) (acti v)

         Glue ts u         -> glue (acti ts) (acti u)
         UnGlue ts u       -> UnGlue (acti ts) (acti u)
         GlueElem ts u     -> glueElem (acti ts) (acti u)
         HisoProj n e      -> HisoProj n (acti e)
         GlueLine t phi psi -> glueLine (acti t) (acti phi) (acti psi)
         GlueLineElem t phi psi -> glueLineElem (acti t) (acti phi) (acti psi)

         VExt psi f g p -> vext (acti psi) (acti f) (acti g) (acti p)

         VPCon n vs phi u v -> pathCon n (acti vs) (acti phi) (acti u) (acti v)
         VHSplit u v        -> app is (acti u) (acti v)

         UnGlueNe u v       -> app is (acti u) (acti v)

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

         VVar x            -> VVar x
         VAppFormula u psi -> VAppFormula (sw u) (sw psi)
         VApp u v          -> VApp (sw u) (sw v)
         VSplit u v        -> VSplit (sw u) (sw v)

         Glue ts u         -> Glue (sw ts) (sw u)
         UnGlue ts u       -> UnGlue (sw ts) (sw u)
         GlueElem ts u     -> GlueElem (sw ts) (sw u)
         HisoProj n e      -> HisoProj n (sw e)
         GlueLine t phi psi -> GlueLine (sw t) (sw phi) (sw psi)
         GlueLineElem t phi psi -> GlueLineElem (sw t) (sw phi) (sw psi)

         VExt psi f g p -> VExt (sw psi) (sw f) (sw g) (sw p)

         VPCon n vs phi u v -> pathCon n (sw vs) (sw phi) (sw u) (sw v)
         VHSplit u v        -> VHSplit (sw u) (sw v)

         UnGlueNe u v       -> UnGlueNe (sw u) (sw v)

instance Nominal Hiso where
--  support (Hiso a b f g s t)  = support (a,b,f,g,s,t)

  act is (Hiso a b f g s t) iphi = Hiso a' b' f' g' s' t'
    where (a',b',f',g',s',t') = act is (a,b,f,g,s,t) iphi

  swap (Hiso a b f g s t) ij = Hiso a' b' f' g' s' t'
    where (a',b',f',g',s',t') = swap (a,b,f,g,s,t) ij

instance Nominal Env where
  -- support Empty          = []
  -- support (Pair e (_,v)) = support (e, v)
  -- support (PDef _ e)     = support e

  act is e iphi  = mapEnv (\u -> act is u iphi) e

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

-- TO CHECK: this is confluent

glueLine :: Val -> Formula -> Formula -> Val
glueLine t _ (Dir Zero) = t
glueLine t (Dir _) _ = t
glueLine t phi (Dir One)  = glue hisos t
  where hisos = mkSystem (map (\ alpha -> (alpha,idHiso (t `face` alpha))) (invFormula phi Zero))
glueLine t phi psi = GlueLine t phi psi

idHiso :: Val -> Hiso
idHiso a = Hiso a a idV idV refl refl
  where idV  = Ter (Lam (noLoc "x") (Var "x")) Empty
        refl = Ter (Lam (noLoc "x") (App (App (PN Refl) (Var "y")) (Var "x")))
                 (Pair Empty ((noLoc "y"),a))

glueLineElem :: Val -> Formula -> Formula -> Val
glueLineElem u (Dir _) _    = u
glueLineElem u _ (Dir Zero) = u
glueLineElem u phi (Dir One)  = glueElem ss u
 where ss = mkSystem (map (\alpha -> (alpha,u `face` alpha)) (invFormula phi Zero))
glueLineElem u phi psi      = GlueLineElem u phi psi

unGlueLine :: Val -> Formula -> Formula -> Val -> Val
unGlueLine b phi psi u =
 case (phi,psi,u) of
   (Dir _,_,_) -> u
   (_,Dir Zero,_) -> u
   (_,Dir One,_) ->
      let hisos  = mkSystem (map (\ alpha -> (alpha,idHiso (b `face` alpha))) (invFormula phi Zero))
      in app (UnGlue hisos b) u
   (_,_,GlueLineElem w _ _ ) -> w
   (_,_,KanUElem _ (GlueLineElem w _ _ )) -> w
   (_,_,_) ->  error ("UnGlueLine, should be GlueLineElem " <+> show u)

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
app :: [Name] -> Val -> Val -> Val
app is (Ter (Lam x t) e) u                = eval is (Pair e (x,u)) t
app is kan@(Kan i b@(VPi a f) ts li0) ui1 =
  -- DT.trace "app Kan VPi" $
    let -- j   = fresh (kan,ui1)
        j   = gensym is
        (aj,fj,tsj) = (a,f,ts) `swap` (i,j)
        u   = fill (j:s) Neg j aj Map.empty ui1
        --ui0 = u `face` (j ~> 0)
        ui0 = comp (j:s) Neg j aj Map.empty ui1
    in comp (j:s) Pos j (app fj u)
           (Map.intersectionWith (app (j:s)) tsj (border u tsj))
           (app is li0 ui0)
app is u@(Ter (Split _ _) _) (KanUElem _ v) = app is u v
app is (Ter (Split _ nvs) e) (VCon name us) = case lookup name nvs of
  Just (xs,t)  -> eval is (upds e (zip xs us)) t
  Nothing -> error $ "app: Split with insufficient arguments; " ++
                        "missing case for " ++ name


-- TODO: is this correct even for HITs???
app is u@(Ter (HSplit _ _ hbr) e) (KanUElem _ v) = app is u v

app is (Ter (HSplit _ _ hbr) e) (VCon name us) =
  case lookup name (zip (map hBranchToLabel hbr) hbr) of
    Just (Branch _ xs t)  -> eval is (upds e (zip xs us)) t
    _ -> error ("app: HSplit with insufficient arguments;"
                <+> "missing case for " <+> name <+> show hbr)

app is (Ter (HSplit _ _ hbr) e) (VPCon name us phi _ _) =
  case lookup name (zip (map hBranchToLabel hbr) hbr) of
    Just (HBranch _ xs t) -> appFormula is (eval is (upds e (zip xs us)) t) phi
    _ -> error ("app: HSplit with insufficient arguments;"
                <+> "missing case for " <+> name <+> show hbr)

app is u@(Ter (HSplit _ f hbr) e) kan@(Kan i v ws w) = -- v should be corr. hsum
  let --j     = fresh (mapEnv ff e,kan)
      j     = gensym is
      wsij  = ws `swap` (i,j)
      ws'   = Map.mapWithKey (\alpha -> app (j:s) (u `face` alpha)) wsij
      w'    = app is u w  -- app (u `face` (i ~> 0)) w
      ffill = app (j:s) (eval (j:s) e f) (fill Pos j (v `swap` (i,j)) wsij w)
  in comp (j:s) Pos j ffill ws' w'

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
    | otherwise              = kanUElem (Map.mapWithKey (\alpha hisoAlpha ->
                                 app is (hisoF hisoAlpha) (w `face` alpha))
                               hisos) w

-- TODO: recheck at least 1 more time (please decrease the counter if
-- you checked)
app is (HisoProj hisoProj e) u = -- DT.trace "app HisoProj" $
  case hisoProj of
    HisoSign sign -> comp (i:s) sign i (appFormula (i:is) e i) Map.empty u
    -- f (g y) -> y
    IsSection     ->
      let ts = Map.fromList [(i ~> 0, line Pos j (appiso Neg u)), (i ~> 1, u)]
      in  Path i $ comp (i:j:s) Pos j (appFormula (i:j:is) e (Atom i :\/: Atom j)) ts (line Neg i u)
    -- g (f x) -> x
    IsRetraction ->
      let ts = Map.fromList [(i ~> 0, u), (i ~> 1, line Neg j (appiso Pos u))]
      in Path i $
           sym (i:j:is) (comp (i:j:s) Neg j (appFormula (i:j:is) e (Atom i :/\: Atom j)) ts (line Pos i u)) i
  where i:j:_ = gensyms is
        appiso sign v = app is (HisoProj (HisoSign sign) e) v
        line sign k v = fill (i:j:s) sign k (e @@ k) Map.empty v

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
gradLemma is hiso@(Hiso a b f g s t) us v =
--  trace ("gradLemma \n b = " ++ show b ++ "\n v = " ++ show v)
  trace "gradLemma" $
    (u, Path i theta'')
  where i:j:_   = gensyms is
        is'     = i:j:is
        us'     = Map.mapWithKey (\alpha uAlpha ->
                                   appFormula is' (app is' (face is' t alpha) uAlpha) i) us
        theta   = fill is' Pos i a us' (app g v)
        --u       = theta `face` (i ~> 1)
        u       = comp is' Pos i a us' (app g v)
        ws      = insertSystem (i ~> 0) (app is' g v) $
                  insertSystem (i ~> 1) (app is' t u @@ j) $
                  Map.mapWithKey
                    (\alpha uAlpha ->
                      appFormula is' (app is' (face is' t alpha) uAlpha) (Atom i :/\: Atom j)) us
        theta'  = comp is' Neg j a ws theta
        xs      = insertSystem (i ~> 0) (appFormula is' (app is' s v) j) $
                  insertSystem (i ~> 1) (appFormula is' (app is' s (app is' f u)) j) $
                  Map.mapWithKey
                    (\alpha uAlpha ->
                      appFormula is' (app is' (face is' s alpha) (app is' (face is' f alpha) uAlpha)) j) us
        theta'' = comp is' Pos j b xs (app f theta')


-- any equality defines an equivalence Lemma 4.2
eqLemma :: [Name] -> Val -> System Val -> Val -> (Val, Val)
eqLemma is e ts a = trace "eqLemma" $
                 (t, Path j theta'')
  where i:j:_   = gensym is
        is'     = i:j:is
        ei      = appFormula is e i
        vs      = Map.mapWithKey (\alpha uAlpha ->
                    fill is' Pos i (face is' ei alpha) Map.empty uAlpha) ts
        theta   = fill is' Neg i ei vs a
        t       = comp is' Neg i ei vs a
        --t       = theta `face` (i ~> 0)
        theta'  = fill is' Pos i ei Map.empty t
        ws      = insertSystem (j ~> 1) theta' $
                  insertSystem (j ~> 0) theta $ vs
        theta'' = comp is' Pos i ei ws t


eqHiso :: Val -> Hiso
eqHiso e = Hiso (e @@ Zero) (e @@ One)
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
      in Ter (mkLams binders $ mkApps (PN pn) (ts ++ vars)) e
  | otherwise =
      let (args,rest) = splitAt (arity pn) ts
          vas = map (eval is e) args
          freshs = gensyms is
          p   = evalPN is freshs pn vas
          r   = map (eval is e) rest
      in apps (take 3 freshs ++ is) p r -- TODO: ugly magic number; calculate vars in evalPN

-- Evaluate primitive notions
evalPN :: [Name] -> [Name] -> PN -> [Val] -> Val
evalPN is (i:_) Id            [a,a0,a1]     = VId (Path i a) a0 a1
evalPN is (i:_) IdP           [_,_,p,a0,a1] = VId p a0 a1
evalPN is (i:_) Refl          [_,a]         = Path i a
evalPN is (i:_) Sym           [_,_,_,p]     = Path i $ p @@ (NegAtom i)
evalPN is (i:_) TransU        [_,_,p,t]     = trace ("evalPN TransU") $
                                           comp (i:is) Pos i (appFormula (i:is) p i) Map.empty t
evalPN is (i:_) TransInvU     [_,_,p,t]     = trace "evalPN TransInvU" $
                                           comp (i:is) Neg i (p @@ i) Map.empty t
evalPN is (i:j:_) CSingl [_,_,_,p] = trace "CSingl"
                                  Path i $ VSPair q (Path j (connect (i:j:is) q (i,j)))
  where q = appFormula (i:is) p i
evalPN is (i:_) Ext [_,_,f,g,p] = Path i $ VExt (Atom i) f g p
evalPN is (i:_)   IsoId    [a,b,f,g,s,t]   =
  Path i $ Glue (mkSystem [(i ~> 0, Hiso a b f g s t)]) b
evalPN is (i:j:_) IsoIdRef [a] = Path j $ Path i $ GlueLine a (Atom i) (Atom j)
evalPN is (i:_)   MapOnPath  [_,_,f,_,_,p]    = Path i $ app (i:is) f (appFormula (i:is) p i)
evalPN is (i:_)   MapOnPathD [_,_,f,_,_,p]    = Path i $ app (i:is) f (appFormula (i:is) p i)
evalPN is (i:_)   AppOnPath [_,_,_,_,_,_,p,q] = Path i $ app (i:is) (appFormula (i:is) p i) (appFormula (i:is) q i)
evalPN is (i:_)   MapOnPathS [_,_,_,f,_,_,p,_,_,q] =
  Path i $ app (i:is) (app (i:is) f (appFormula (i:is) p i)) (appFormula (i:is) q i)
evalPN is (i:j:k:_) LemSimpl [v,a,b,c,p,q,q',s] =
  Path j $ Path k $ comp is' Pos i v ss a
   where ss = mkSystem [(j ~> 0,fill is' Pos k v (mkSystem [(i ~> 0,a),(i ~> 1,appFormula is' q j)]) (appFormula is' p i)),
                        (j ~> 1,fill is' Pos k v (mkSystem [(i ~> 0,a),(i ~> 1,appFormula is' q' j)]) (appFormula is' p i)),
                        (k ~> 0,appFormula is' (appFormula is' p i)),
                        (k ~> 1,appFormula is' (appFormula is' s j) i)]
         is' = i:j:k:is
evalPN is (i:j:_) Transpose [t,a0,a1,u,b0,b1,v,r0,r1,x] =
   Path j $ Path i $ (appFormula (i:is) (appFormula is x i) j)
evalPN is (i:j:_) IdSElim [a,b,p,u,v,x] =
   Path j $ comp (i:j:is) Pos i (appFormula (i:j:is) p i) ss u
     where ss = mkSystem [(j ~> 1, appFormula (i:j:is) x i)]
evalPN is _       u          _                = error ("evalPN " ++ show u)

{-

Id (<i0> Id p (q @ Atom i0) (comp Pos i (p @@ i) Map.empty (q @ Atom i0)))
   (Path i $ fill Pos i (p @@ i) Map.empty u)
   (Path i $ fill Pos i (p @@ i) Map.empty u)

-}
-- we add as a primitive that (A B:U) -> prop A -> prop (Id U A B), i, j free
-- propId a b pa x y i j = Path j rem
--  where comp Pos i v 
--       v = apps VId [VU,a,b]




comps :: [Name] -> Name -> [(Binder,Ter)] -> Env -> [(System Val,Val)] -> [Val]
comps is i []         _ []         = []
comps is i ((x,a):as) e ((ts,u):tsus) =
  let v  = fill is Pos i (eval (i:is) e a) ts u
      -- vi1 = v `face` (i ~> 1)
      vi1 = comp is Pos i (eval (i:is) e a) ts u
      vs  = comps is i as (Pair e (x,v)) tsus
  in vi1 : vs
comps _ _ _ _ = error "comps: different lengths of types and values"

fills :: Name -> [(Binder,Ter)] -> Env -> [(System Val,Val)] -> [Val]
fills i []         _ []         = []
fills i ((x,a):as) e ((ts,u):tsus) =
  let v  = fill Pos i (eval (i:is) e a) ts u
      -- vi0 = v `face` (i ~> 1)
      vs  = fills i as (Pair e (x,v)) tsus
  in v : vs
fills _ _ _ _ = error "fills: different lengths of types and values"

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
fill is Neg i a ts u =  trace "fill Neg" $  -- i should be in is (added just to be sure)
  sym (i:is) (fill is Pos i (sym (i:is) a i) (sym (i:is) ts i) u) i
fill is Pos i a ts u =  trace "fill Pos" $
  comp (i:j:is) Pos j (connect (i:j:is) a (i, j)) (connect (i:j:is) ts (i, j)) u
  where j = gensym (i:is)

comp :: [Name] -> Sign -> Name -> Val -> System Val -> Val -> Val
-- Not possible to optimize w/o calculating the support.
-- comp is sign i a ts u | i `notElem` support (a,ts) =
--    -- DT.trace "comp cheaply regular" $
--    u
-- -- Another possible optimization:
-- comp is sign i a ts u | i `notElem` support a && not (Map.null indep) =
--   -- DT.trace "comp filter" $
--   comp is sign i a ts' u
--   where (ts',indep) = Map.partition (\t -> i `elem` support t) ts
comp is Neg i a ts u = trace "comp Neg" $ comp is Pos i (sym (i:is) a i) (sym (i:is) ts i) u

-- If 1 is a key of ts, then it means all the information is already there.
-- This is used to take (k = 0) of a comp when k \in L
comp is Pos i a ts u | eps `Map.member` ts = -- DT.trace "easy case of comp" $
  act (i:is) (ts ! eps) (i,Dir 1)
comp is Pos i (KanUElem _ a) ts u = comp is Pos i a ts u
comp is Pos i vid@(VId a u v) ts w = -- DT.trace "comp VId" $
    Path j $ comp (i:j:is) Pos i (a @@ j) ts' (w @@ j)
  where j   = gensym (i:is)
        ts' = insertSystem (j ~> 0) u $
              insertSystem (j ~> 1) v $
              Map.map (\u -> appFormula (i:is) u j) ts
comp is Pos i b@(VSigma a f) ts u = -- DT.trace "comp VSigma" $
  VSPair ui1 comp_u2
  where (t1s, t2s) = (Map.map fstSVal ts, Map.map sndSVal ts)
        (u1,  u2)  = (fstSVal u, sndSVal u)
        fill_u1    = fill (i:is) Pos i a t1s u1
        --ui1        = fill_u1 `face` (i ~> 1)
        ui1        = comp is Pos i a t1s u1
        comp_u2    = comp is Pos i (app f fill_u1) t2s u2

comp is Pos i a@VPi{} ts u   = Kan i a ts u

comp is Pos i g@(Glue hisos b) ws wi0 =
  trace ("comp Glue") $ -- \n ShapeOk: " ++ show (shape usi1 == shape hisosI1))
    glueElem usi1 vi1''
  where unglue = UnGlue hisos b
        vs   = Map.mapWithKey
                 (\alpha wAlpha -> app (unglue `face` alpha) wAlpha) ws
        vi0  = app (unglue `face` (i ~> 0)) wi0 -- in b(i0)

        v    = fill Pos i b vs vi0           -- in b
        --vi1  = v `face` (i ~> 1)
        vi1  = comp is Pos i b vs vi0           -- in b(i1)

        hisosI1 = hisos `face` (i ~> 1)
        -- (hisos', hisos'') = Map.partitionWithKey
        --                     (\alpha _ -> alpha `Map.member` hisos) hisosI1

        hisos'' = Map.filterWithKey (\alpha _ -> not (alpha `Map.member` hisos)) hisosI1

        -- set of elements in hisos independent of i
        --hisos'  = Map.filterWithKey (\alpha _ -> not (leq alpha (i ~> 1))) hisos
        hisos'  = Map.filterWithKey (\alpha _ -> i `Map.notMember` alpha) hisos

        us'    = Map.mapWithKey (\gamma (Hiso aGamma _ _ _ _ _) ->
                  fill Pos i aGamma (ws `face` gamma) (wi0 `face` gamma))
                hisos'
        usi1'  = Map.mapWithKey (\gamma (Hiso aGamma _ _ _ _ _) ->
                  comp is Pos i aGamma (ws `face` gamma) (wi0 `face` gamma))
                hisos'
        --usi1'  = Map.map (\u -> u `face` (i ~> 1)) us'

        ls'    = Map.mapWithKey (\gamma (Hiso aGamma bGamma fGamma _ _ _) ->
                  pathComp i bGamma (vs `face` gamma)
                    (v `face` gamma) (fGamma `app` (us' ! gamma)))
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

comp is Pos i t@(Kan j VU ejs b) ws wi0 =
    let es    = Map.map (Path j . (`sym` j)) ejs
        hisos = Map.map eqHiso es
        unkan = UnKan hisos b

        vs    = Map.mapWithKey (\alpha wAlpha -> app (unkan `face` alpha) wAlpha) ws
        vi0   = app (unkan `face` (i ~> 0)) wi0 -- in b(i0)

        vi1     =  comp is Pos i b vs vi0           -- in b(i1)

        hisosI1 = hisos `face` (i ~> 1)

        --  {(gamma, sigma gamma (i1)) | gamma elem hisos}
        hisos'' = Map.filterWithKey (\alpha _ -> not (alpha `Map.member` hisos)) hisosI1

        -- set of elements in hisos independent of i
        --hisos'  = Map.filterWithKey (\alpha _ -> not (leq alpha (i ~> 1))) hisos
        hisos'  = Map.filterWithKey (\alpha _ -> i `Map.notMember` alpha) hisos

        -- (hisos', hisos'') = Map.partitionWithKey
        --                     (\alpha _ -> alpha `Map.member` hisos) hisosI1

        usi1'    = Map.mapWithKey (\gamma (Hiso aGamma _ _ _ _ _) ->
                     comp is Pos i aGamma (ws `face` gamma) (wi0 `face` gamma))
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


comp is Pos i (GlueLine b phi psi) us u = -- DT.trace "comp GlueLine" $
                                       glueLineElem vm phii1 psii1
  where
         phii1   = phi `face` (i ~> 1)
         psii1   = psi `face` (i ~> 1)
         phii0   = phi `face` (i ~> 0)
         psii0   = psi `face` (i ~> 0)
         bi1 = b `face`  (i ~> 1)
         bi0 = b `face`  (i ~> 0)
         lss = mkSystem (map (\ alpha -> (alpha,(face phi alpha,face b alpha,face us alpha,face u alpha))) fs)
         ls = Map.mapWithKey (\alpha vAlpha -> auxGlueLine i vAlpha (v `face` alpha)) lss
         v = comp Pos i b ws w
         ws = Map.mapWithKey (\alpha -> unGlueLine (face b alpha) (face phi alpha) (face psi alpha)) us
         w  = unGlueLine bi0 phii0 psii0 u
         vm = compLine (b `face` (i ~>1)) ls v
         fs = filter (i `Map.notMember`) (invFormula psi One)

comp is Pos i VU ts u = Kan i VU ts u

comp is Pos i v@(Ter (Sum _ _) _) tss (KanUElem _ w) = comp is Pos i v tss w

comp is Pos i a ts u | isNeutral a || isNeutralSystem ts || isNeutral u =
  trace "comp Neutral"
  -- ++ show a ++ "\n i=" ++ show i ++ "\n ts = " ++ show ts ++ "\n u = " ++ show u)
  KanNe i a ts u

comp is Pos i v@(Ter (Sum _ nass) env) tss (VCon n us) = -- DT.trace "comp Sum" $
  case getIdent n nass of
  Just as -> VCon n $ comps i as env tsus
    where tsus = transposeSystemAndList (Map.map unCon tss) us
  Nothing -> error $ "comp: missing constructor in labelled sum " ++ n

-- Treat transport in hsums separately.
comp is Pos i v@(Ter (HSum _ hls) env) us u | Map.null us =
  DT.trace "comp HSum us empty" $
  case u of
  VCon c ws -> case getIdent c (map hLabelToBinderTele hls) of
    Just as -> VCon c (comps i as env (zip (repeat Map.empty) ws))
    Nothing -> error $ "comp HSum: missing constructor in hsum" <+> c
  VPCon c ws0 phi e0 e1 -> case getIdent c (mapHLabelToBinderTele hls) of -- u should be independent of i, so i # phi
    Just (as, _,_) ->VPCon c ws1 phi (tr e0) (tr e1)
      where  -- The following seems correct when [phi] is a variable, but
             -- otherwise we need to do an induction on [phi]
        tr  = comp is Pos i v Map.empty
        ws1 = comps i as env (zip (repeat Map.empty) ws0)
    Nothing -> error $ "comp HSum: missing path constructor in hsum" <+> c
  Kan j b ws w -> comp is Pos k vi1 ws' (transp (i ~> 1) w)
    where vi1 = v `face` (i ~> 1)  -- b is vi0 and independent of j
          k   = gensym (support (v,u,Atom i))
          transp alpha = comp is Pos i (v `face` alpha) Map.empty
          wsjk         = ws `swap` (j,k)
          ws'          = Map.mapWithKey transp wsjk
  u | isNeutral u -> KanNe i v us u
  KanUElem _ u1 -> comp is Pos i v us u1
  u -> error $ "comp HSum:" <+> show u <+> "should be neutral"

comp is Pos i v@(Ter (HSum _ _) _) us u =
  -- DT.trace "comp HSum us nonempty" $
  if i `notElem` support us'
  then transp i v u
  else Kan i (vi1) us' (transp i v u)
  where vi1         = v `face` (i ~> 1)
        j           = gensym (support (v,us,u,Atom i))
        comp' alpha = transp j ((v `face` alpha) `act` (i, Atom i:\/: Atom j))
        us'         = Map.mapWithKey comp' us
        transp j w  = comp is Pos j w Map.empty

comp is Pos i a ts u =
  error $
  "comp _: not implemented for \n a = " <+> show a <+> "\n" <+>
  "ts = " <+> show ts <+> "\n" <+>
  "u = " <+> parens (show u)

-- Lemma 2.1
-- assumes u and u' : A are solutions of us + (i0 -> u(i0))
-- (in the Pos case, otherwise we symmetrize)
-- The output is an L-path in A(i1) between u(i1) and u'(i1)
pathComp :: Name -> Val -> System Val -> (Val -> Val -> Val)
pathComp i a us u u' = trace "pathComp"
                       Path j $ comp Pos i a us' (u `face` (i ~> 0))
  where j   = fresh (Atom i, a, us, u, u')
        us' = insertsSystem [(j ~> 0, u), (j ~> 1, u')] us

-- Lemma 6.1 Computes a homotopy between the image of the composition,
-- and the composition of the image.  Given e (an equality in U), an
-- L-system us (in e0) and ui0 (in e0 (i0)) The output is an L(i1)-path in
-- e1(i1) between vi1 and sigma (i1) ui1 where
--   sigma = HisoProj (ProjSign Pos) e
--   ui1 = comp Pos i (e 0) us ui0
--   vi1 = comp Pos i (e 1) (sigma us) (sigma(i0) ui0)
-- Moreover, if e is constant, so is the output.
pathUniv :: Name -> Val -> System Val -> Val -> Val
pathUniv i e us ui0 = Path k xi1
  where j:k:_ = freshs (Atom i, e, us, ui0)
        -- f     = HisoProj (HisoSign Pos) e
        ej    = e @@ j
        ui1   = comp Pos i (e @@ Zero) us ui0
        ws    = Map.mapWithKey (\alpha uAlpha ->
                  fill Pos j (ej `face` alpha) Map.empty uAlpha)
                us
        wi0   = fill Pos j (ej `face` (i ~> 0)) Map.empty ui0
        wi1   = comp Pos i ej ws wi0
        wi1'  = fill Pos j (ej `face` (i ~> 1)) Map.empty ui1
        xi1   = comp Pos j (ej `face` (i ~> 1))
                  (insertsSystem [(k ~> 1, wi1'), (k ~> 0, wi1)] Map.empty) ui1


-- Lemma 2.2
-- takes a type A, an L-system of lines ls and a value u
-- s.t. ls alpha @@ 0 = u alpha
-- and returns u' s.t. ls alpha @@ 1 = u' alpha
compLine :: Val -> System Val -> Val -> Val
compLine a ls u = trace ("compLine \n a=" ++ show a ++ "\n u = " ++ show u)
  comp Pos i a (Map.map (@@ i) ls) u  -- TODO also check pathComp; are
                                      -- the dirs correct?
  where i = fresh (a, ls, u)

-- the same but now computing the line
fillLine :: Val -> System Val -> Val -> Val
fillLine a ls u = trace ("compLine \n a=" ++ show a ++ "\n u = " ++ show u)
  Path i (fill Pos i a (Map.map (@@ i) ls) u)
  where i = fresh (a, ls, u)

class Convertible a where
  conv   :: Int -> a -> a -> Bool

instance Convertible Val where
  conv _ u v | u == v = True
  conv k VU VU                                  = True
  conv k w@(Ter (Lam x u) e) w'@(Ter (Lam x' u') e') =
    let v = mkVar k
    in trace ("conv Lam Lam \n w = " ++ show w ++ " \n w' = " ++ show w')
     conv (k+1) (eval (Pair e (x,v)) u) (eval (Pair e' (x',v)) u')
  conv k w@(Ter (Lam x u) e) u' =
    let v = mkVar k
    in trace ("conv Lam u' \n w = " ++ show w ++ " \n u' = " ++ show u')
        conv (k+1) (eval (Pair e (x,v)) u) (app u' v)
  conv k u' w'@(Ter (Lam x u) e) =
    let v = mkVar k
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
    let w = mkVar k
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
    where w = mkVar k
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
  conv k v@(KanNe i a ts u) v'@(KanNe i' a' ts' u') =
     trace ("conv KanNe" ++ "\n   v = " ++ show v ++ "\n    v' = " ++ show v')  $
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
  conv k u@(UnGlue hisos v) u'@(UnGlue hisos' v') = conv k hisos hisos' && conv k v v'

  conv k u@(HisoProj{}) u'@(HisoProj{}) = conv (k+1) (app u w) (app u' w)
       where w = mkVar k

  conv k (VExt phi f g p) (VExt phi' f' g' p') =
    conv k (phi,f,g,p) (phi',f',g',p')

  conv k u@(VExt phi f g p) u' = conv (k+1) (app u w) (app u' w)
    where w = mkVar k

  conv k u u'@(VExt phi f g p) = conv (k+1) (app u w) (app u' w)
    where w = mkVar k

  conv k (VVar x)  (VVar x')             = x == x'
  conv k (VApp u v)     (VApp u' v')     = conv k u u' && conv k v v'
  conv k (VAppFormula u x) (VAppFormula u' x') = conv k u u' && (x == x')
  conv k (VSplit u v)   (VSplit u' v')   = conv k u u' && conv k v v'
  conv k (VHSplit u v)  (VHSplit u' v')  = conv k u u' && conv k v v'
  conv k (UnGlueNe u v) (UnGlueNe u' v') = conv k u u' && conv k v v'
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
    where v@(VVar name) = mkVar k
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
  normal k (GlueLine u phi psi) = glueLine (normal k u) phi psi
  normal k (GlueLineElem u phi psi) = glueLineElem (normal k u) phi psi

  normal k (VExt phi u v w) = VExt phi u' v' w'
    where (u',v',w') = normal k (u,v,w)

  normal k (VApp u v) = app (normal k u) (normal k v)
  normal k (VAppFormula u phi) = normal k u @@ phi
  normal k (VFst u) = fstSVal (normal k u)
  normal k (VSnd u) = sndSVal (normal k u)
  normal k (VSplit u v) = VSplit (normal k u) (normal k v)

  normal k (VHSplit u v) = VHSplit (normal k u) (normal k v)
  normal k (VPCon n us phi u0 u1) =
    VPCon n (normal k us) phi (normal k u0) (normal k u1)

  normal k (UnGlueNe u v) = UnGlueNe (normal k u) (normal k v)

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

-- auxiliary function needed for composition for GlueLine

auxGlueLine :: Name -> (Formula,Val,System Val,Val) -> Val -> Val
auxGlueLine i (Dir _,b,ws,wi0) vi1 = Path j vi1 where j = fresh vi1
auxGlueLine i (phi,b,ws,wi0) vi1   = fillLine (b `face` (i ~> 1)) ls' vi1
  where unglue = UnGlue hisos b
        hisos = mkSystem (map (\ alpha -> (alpha,idHiso (b `face` alpha))) (invFormula phi Zero))
        vs   = Map.mapWithKey (\alpha -> app (unglue `face` alpha)) ws
        vi0  = app (unglue `face` (i ~> 0)) wi0 -- in b(i0)

        v    = fill Pos i b vs vi0           -- in b

        -- set of elements in hisos independent of i
        hisos'  = Map.filterWithKey (\alpha _ -> i `Map.notMember` alpha) hisos

        us'    = Map.mapWithKey (\gamma (Hiso aGamma _ _ _ _ _) ->
                  fill Pos i aGamma (ws `face` gamma) (wi0 `face` gamma))
                hisos'

        ls'    = Map.mapWithKey (\gamma (Hiso aGamma _ _ _ _ _) ->
                  pathComp i aGamma (vs `face` gamma) (v `face` gamma) (us' ! gamma))
                 hisos'

