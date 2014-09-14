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
  support (VId a v0 v1)                 = support [a,v0,v1]
  support (Path i v)                    = i `delete` support v

  support (VSigma u v)                  = support (u,v)
  support (VSPair u v)                  = support (u,v)
  support (VFst u)                      = support u
  support (VSnd u)                      = support u

  support (VCon _ vs)                   = support vs

  support (VVar i)                      = []
  support (VApp u v)                    = support (u, v)
  support (VAppFormula u phi)           = support (u, phi)
  support (VSplit u v)                  = support (u, v)

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


  act u (i, phi) = trace ("act" <+> show u <+> parens (show i <+> "=" <+> show phi)) $
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

         VId a u v -> VId (acti a) (acti u) (acti v)
         Path j v -> Path k (acti (v `rename` (j,k)))
              where k = fresh (v, Atom i, phi)

         VSigma a f -> VSigma (acti a) (acti f)
         VSPair u v -> VSPair (acti u) (acti v)
         VFst u     -> VFst (acti u)
         VSnd u     -> VSnd (acti u)

         VCon c vs  -> VCon c (acti vs)

         VVar x            -> VVar x
         VAppFormula u psi -> acti u @@ acti psi
         VApp u v          -> app (acti u) (acti v)
         VSplit u v        -> app (acti u) (acti v)

instance Nominal Env where
  act e iphi = mapEnv (\u -> act u iphi) e

  support Empty          = []
  support (Pair e (_,v)) = support (e, v)
  support (PDef _ e)     = support e

-- Application
app :: Val -> Val -> Val
app (Ter (Lam x t) e) u            = eval (Pair e (x,u)) t
app (Kan i b@(VPi a f) ts li0) ui1 = trace "app (Kan VPi)" $
    let j   = fresh (b,u,ts)
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
app u@(Ter (Split _ _) _) v
  | isNeutral v = VSplit u v -- v should be neutral
  | otherwise   = error $ "app: (VSplit) " ++ show v ++ " is not neutral"
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

(@@) :: Val -> Formula -> Val
(Path i u) @@ phi = u `act` (i, phi)
v @@ phi          = VAppFormula v phi

(@@@) :: Val -> Name -> Val
p @@@ i = p @@ Atom i

-- where j = fresh (u, Atom i, phi)
-- | y `elem` [0,1] = u `face` (x,y)
-- appFormula p y          | y `elem` [0,1] = VAppFormula p y -- p has to be neutral
-- appFormula (Path x u) y | x == y             = u
--                      | y `elem` support u = error ("appFormula " ++ "\nu = " ++
--                                                    show u ++ "\ny = " ++ show y)
--                      | otherwise          = swap u x y
-- appFormula v y          = VAppFormula v y

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
evalPN (i:_) TransU        [_,_,p,t]     = trace "evalPN TransU" $ comp Pos i (p @@@ i) Map.empty t
evalPN (i:_) TransInvU     [_,_,p,t]     = comp Neg i (p @@@ i) Map.empty t
-- figure out how to turn TransURef into a definitional equality (pb for neutral terms)
evalPN (i:_) TransURef     [a,t]         = Path i $ fill Pos i a Map.empty t
-- evalPN (x:_) TransUEquivEq [_,b,f,_,_,u] =
--   Path x $ fill b (Box up x (app f u) [])   -- TODO: Check this!
-- evalPN (x:y:_) CSingl [a,u,v,p] =
--   let pv    = appFormula p y
--       theta = fill a (Box up y u [((x,down),u),((x,up),pv)])
--       omega = theta `face` (y,up)
--   in Path x (VSPair omega (Path y theta))
-- -- evalPN (x:_)   Ext        [_,b,f,g,p]   = return $ Path x $ VExt x b f g p
-- evalPN (x:_)   HExt       [_,b,f,g,p]   = Path x $ VHExt x b f g p
-- evalPN _       Inh        [a]           = VInh a
-- evalPN _       Inc        [_,t]         = VInc t
-- evalPN (x:_)   Squash     [_,r,s]       = Path x $ VSquash x r s
-- evalPN _       InhRec     [_,b,p,phi,a] = inhrec b p phi a
-- evalPN (x:_)   EquivEq    [a,b,f,s,t]   = Path x $ VEquivEq x a b f s t
-- evalPN (x:y:_) EquivEqRef [a,s,t]       =
--   Path y $ Path x $ VEquivSquare x y a s t
evalPN (i:_)   MapOnPath  [_,_,f,_,_,p]    = Path i $ app f (p @@@ i)
evalPN (i:_)   MapOnPathD [_,_,f,_,_,p]    = Path i $ app f (p @@@ i)
evalPN (i:_)   AppOnPath [_,_,_,_,_,_,p,q] = Path i $ app (p @@@ i) (q @@@ i)
evalPN (i:_)   MapOnPathS [_,_,_,f,_,_,p,_,_,q] = 
  Path i $ app (app f (p @@@ i)) (q @@@ i)
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

-- faceName :: Name -> Face -> Name
-- faceName 0 _                 = 0
-- faceName 1 _                 = 1
-- faceName x (y,d) | x == y    = d
--                  | otherwise = x

-- -- Compute the face of a value
-- face :: Val -> Side -> Val
-- face u xdir@(x,dir) =
--   let fc v = v `face` xdir in case u of
--   VU      -> VU
--   Ter t e -> eval (e `faceEnv` xdir) t
--   VId a v0 v1 -> VId (fc a) (fc v0) (fc v1)
--   Path y v | x == y    -> u
--            | otherwise -> Path y (fc v)
--   -- VExt y b f g p | x == y && dir == down -> f
--   --                | x == y && dir == up   -> g
--   --                | otherwise             ->
--   --                  VExt y <$> fc b <*> fc f <*> fc g <*> fc p
--   VHExt y b f g p | x == y && dir == down -> f
--                   | x == y && dir == up   -> g
--                   | otherwise             -> VHExt y (fc b) (fc f) (fc g) (fc p)
--   VPi a f    -> VPi (fc a) (fc f)
--   VSigma a f -> VSigma (fc a) (fc f)
--   VSPair a b -> VSPair (fc a) (fc b)
--   VInh v     -> VInh (fc v)
--   VInc v     -> VInc (fc v)
--   VSquash y v0 v1 | x == y && dir == down -> v0
--                   | x == y && dir == up   -> v1
--                   | otherwise             -> VSquash y (fc v0) (fc v1)
--   VCon c us -> VCon c $ map fc us
--   VEquivEq y a b f s t | x == y && dir == down -> a
--                        | x == y && dir == up   -> b
--                        | otherwise             ->
--                          VEquivEq y (fc a) (fc b) (fc f) (fc s) (fc t)
--   VPair y a v | x == y && dir == down -> a
--               | x == y && dir == up   -> fc v
--               | otherwise             -> VPair y (fc a) (fc v)
--   VEquivSquare y z a s t | x == y                -> a
--                          | x == z && dir == down -> a
--                          | x == z && dir == up   ->
--                            let idV = Ter (Lam (noLoc "x") (Var "x")) oEmpty
--                            in VEquivEq y a a idV s t
--                          | otherwise             ->
--                           VEquivSquare y z (fc a) (fc s) (fc t)
--   VSquare y z v | x == y                -> fc v
--                 | x == z && dir == down -> fc v
--                 | x == z && dir == up   ->
--                   let v' = fc v
--                   in VPair y (v' `face` (y,down)) v'
--                 | otherwise             -> VSquare y z $ fc v
--   Kan Fill a b@(Box dir' y v nvs)
--     | x /= y && x `notElem` nonPrincipal b -> fill (fc a) (mapBox fc b)
--     | x `elem` nonPrincipal b              -> lookBox (x,dir) b
--     | x == y && dir == mirror dir'         -> v
--     | otherwise                            -> com a b
--   VFillN a b@(Box dir' y v nvs)
--     | x /= y && x `notElem` nonPrincipal b -> fill (fc a) (mapBox fc b)
--     | x `elem` nonPrincipal b              -> lookBox (x,dir) b
--     | x == y && dir == mirror dir'         -> v
--     | otherwise                            -> com a b
--   Kan Com a b@(Box dir' y v nvs)
--     | x == y                     -> u
--     | x `notElem` nonPrincipal b -> com (fc a) (mapBox fc b)
--     | x `elem` nonPrincipal b    -> lookBox (x,dir) b `face` (y,dir')
--   VComN a b@(Box dir' y v nvs)
--     | x == y                     -> u
--     | x `notElem` nonPrincipal b -> com (fc a) (mapBox fc b)
--     | x `elem` nonPrincipal b    -> lookBox (x,dir) b `face` (y,dir')
--   VComp b@(Box dir' y _ _)
--     | x == y                     -> u
--     | x `notElem` nonPrincipal b -> VComp $ mapBox fc b
--     | x `elem` nonPrincipal b    -> lookBox (x,dir) b `face` (y,dir')
--   VFill z b@(Box dir' y v nvs)
--     | x == z                               -> u
--     | x /= y && x `notElem` nonPrincipal b -> VFill z $ mapBox fc b
--     | (x,dir) `elem` defBox b              ->
--       lookBox (x,dir) (mapBox (`face` (z,down)) b)
--     | x == y && dir == dir'                ->
--         VComp (mapBox (`face` (z,up)) b)
--   VInhRec b p h a     -> inhrec (fc b) (fc p) (fc h) (fc a)
--   VApp u v            -> app (fc u) (fc v)
--   VAppFormula u n        -> appFormula (fc u) (faceName n xdir)
--   VSplit u v          -> app (fc u) (fc v)
--   VVar s d            -> VVar s [ faceName n xdir | n <- d ]
--   VFst p              -> fstSVal $ fc p
--   VSnd p              -> sndSVal $ fc p
--   VCircle             -> VCircle
--   VBase               -> VBase
--   VLoop y | x == y    -> VBase
--           | otherwise -> VLoop y
--   VCircleRec f b l s  -> circlerec (fc f) (fc b) (fc l) (fc s)
--   VI  -> VI
--   VI0 -> VI0
--   VI1 -> VI1
--   VLine y
--     | x == y && dir == down -> VI0
--     | x == y && dir == up   -> VI1
--     | otherwise             -> VLine y
--   VIntRec f s e l u -> intrec (fc f) (fc s) (fc e) (fc l) (fc u)

-- unCompAs :: Val -> Name -> Box Val
-- unCompAs (VComp box) y = swap box (pname box) y
-- unCompAs v           _ = error $ "unCompAs: " ++ show v ++ " is not a VComp"

-- unFillAs :: Val -> Name -> Box Val
-- unFillAs (VFill x box) y = swap box x y
-- unFillAs v             _ = error $ "unFillAs: " ++ show v ++ " is not a VFill"

-- p(x) = <z>q(x,z)
-- a(x) = q(x,0)     b(x) = q(x,1)
-- q(0,y) connects a(0) and b(0)
-- we connect q(0,0) to q(1,1)
-- appDiag :: Val -> Val -> Name -> Val
-- appDiag tu p x | x `elem` [0,1] = appFormula p x
-- appDiag tu p x =
-- traceb ("appDiag " ++ "\ntu = " ++ show tu ++ "\np = " ++ show p ++ "\nx = "
-- --                       ++ show x ++ " " ++ show y
-- --                       ++ "\nq = " ++ show q) -- "\nnewBox =" ++ show newBox)
--  com tu newBox
--    where y = fresh (p,(tu,x))
--          q = appFormula p y
--          a = appFormula p 0
--          b = appFormula p 1
--          newBox = Box down y b [((x,down),q `face` (x,down)),((x,up),b `face` (x,up))]

-- inhrec :: Val -> Val -> Val -> Val -> Val
-- inhrec _ _ phi (VInc a)          = app phi a
-- inhrec b p phi (VSquash x a0 a1) =
--   let fc w d   = w `face` (x,d)
--       b0       = inhrec (fc b down) (fc p down) (fc phi down) a0
--       b1       = inhrec (fc b up) (fc p up) (fc phi up) a1
--       z        = fresh [b,p,phi,b0,b1]
--       b0fill   = fill b (Box up x b0 [])
--       b0fillx1 = b0fill `face` (x, up)
--       right    = appFormula (app (app (fc p up) b0fillx1) b1) z
--   in com b (Box up z b0fill [((x,down),b0),((x,up),right)])
-- inhrec b p phi (Kan ktype (VInh a) box) =
--   let irec (j,dir) v = let fc v = v `face` (j,dir)
--                        in inhrec (fc b) (fc p) (fc phi) v
--       box' = modBox irec box
--   in kan ktype b box'
-- inhrec b p phi v = VInhRec b p phi v -- v should be neutral

-- circlerec :: Val -> Val -> Val -> Val -> Val
-- circlerec _ b _ VBase       = b
-- circlerec f b l v@(VLoop x) =
--   let y     = fresh [f,b,l,v]
--       pxy   = appFormula l y
--       theta = connection VCircle x y v
--       a     = app f theta
--       px1   = pxy `face` (y,up)
--       p11   = px1 `face` (x,up)
--       p0y   = pxy `face` (x,down)
--   in com a (Box down y px1 [((x,down),p0y),((x,up),p11)])
-- circlerec f b l v@(Kan ktype VCircle box) =
--   let crec side u = let fc w = w `face` side
--                     in circlerec (fc f) (fc b) (fc l) u
--       fv   = app f v
--       box' = modBox crec box
--   in kan ktype fv box'
-- circlerec f b l v = VCircleRec f b l v -- v should be neutral


-- intrec :: Val -> Val -> Val -> Val -> Val -> Val
-- intrec _ s _ _ VI0         = s
-- intrec _ _ e _ VI1         = e
-- intrec f s e l v@(VLine x) =
--   let y     = fresh [f,s,e,l,v]
--       pxy   = appFormula l y
--       theta = connection VI x y v
--       a     = app f theta
--       px1   = pxy `face` (y,up)
--       p11   = px1 `face` (x,up)
--       p0y   = pxy `face` (x,down)
--   in com a (Box down y px1 [((x,down),p0y),((x,up),p11)])
-- intrec f s e l v@(Kan ktype VCircle box) =
--   let irec side u = let fc w = w `face` side
--                     in intrec (fc f) (fc s) (fc e) (fc l) u
--       fv   = app f v
--       box' = modBox irec box
--   in kan ktype fv box'
-- intrec f s e l v = VIntRec f s e l v -- v should be neutral

-- kan :: KanType -> Val -> Box Val -> Val
-- kan Fill = fill
-- kan Com  = com

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
comps :: Name -> [(Binder,Ter)] -> Env -> [System Val] -> [Val] -> [Val]
comps i []         _ []         []      = []
comps i ((x,a):as) e (ts:tss)   (u:us) =
  let v  = comp Pos i (eval e a) ts u
      vs = comps i as (Pair e (x,v)) tss us
  in v : vs
comps _ _ _ _ _ = error "comps: different lengths of types and values"

-- unPack :: Name -> Name -> (Name,Dir) -> Val -> Val
-- unPack x y (z,c) v | z /= x && z /= y  = unSquare v
--                    | z == y && c == up = sndVal v
--                    | otherwise         = v


-- -- Composition (ie., the face of fill which is created)
-- com :: Val -> Box Val -> Val
-- com u box | isNeutralFill u box = VComN u box
-- com vid@VId{} box@(Box dir i _ _)         = fill vid box `face` (i,dir)
-- com vsigma@VSigma{} box@(Box dir i _ _)   = fill vsigma box `face` (i,dir)
-- com veq@VEquivEq{} box@(Box dir i _ _)    = fill veq box `face` (i,dir)
-- com u@(Kan Com VU _) box@(Box dir i _ _)  = fill u box `face` (i,dir)
-- com u@(Kan Fill VU _) box@(Box dir i _ _) = fill u box `face` (i,dir)
-- com ter@Ter{} box@(Box dir i _ _)         = fill ter box `face` (i,dir)
-- com v box                                 = Kan Com v box

isNeutralSystem :: System Val -> Bool 
isNeutralSystem = undefined -- TODO implement!!

data Sign = Pos | Neg

fill :: Sign -> Name -> Val -> System Val -> Val -> Val
fill Neg i a ts u =  trace "fill Neg" $ (fill Pos i (a `sym` i) (ts `sym` i) u) `sym` i
fill Pos i a ts u =  trace "fill Pos" $ comp Pos j (a `connect` (i, j)) (ts `connect` (i, j)) u
  where j = fresh (a,u,ts)

comp :: Sign -> Name -> Val -> System Val -> Val -> Val
comp Neg i a ts u = trace "comp Neg" $ comp Pos i (a `sym` i) (ts `sym` i) u
-- If 1 is a key of ts, then it means all the information is already there.
-- This is used to take (k = 0) of a comp when k \in L
comp Pos i a ts u | Map.empty `Map.member` ts = trace "comp 1" $ (ts ! Map.empty) `act` (i,Dir 1)
comp Pos i a ts u | isNeutral a || isNeutralSystem ts || isNeutral u = Kan i a ts u
comp Pos i vid@(VId a u v) ts w = trace "comp VId"
  Path j $ comp Pos i (a @@@ j) ts' (w @@@ j)
  where j   = fresh (Atom i, vid, ts, w)
        ts' = insertSystem (Map.fromList [(j,0)]) u $
              insertSystem (Map.fromList [(j,1)]) v $
              Map.map (@@@ j) ts
comp Pos i b@(VSigma a f) ts u = VSPair (fill_u1 `act` (i, Dir 1)) comp_u2
  where (t1s, t2s) = (Map.map fstSVal ts, Map.map sndSVal ts)
        (u1,  u2)  = (fstSVal u, sndSVal u)
        fill_u1    = fill Pos i a t1s u1
        comp_u2    = comp Pos i (app f fill_u1) t2s u2

comp Pos i v@(Ter (Sum _ nass) env) tss (VCon n us) = case getIdent n nass of
  Just as -> VCon n $ comps i as env tss' us
    where tss' = transposeSystem $ Map.map unCon tss
  Nothing -> error $ "fill: missing constructor in labelled sum " ++ n

comp Pos i a@VPi{} ts u   = Kan i a ts u
comp Pos i (Kan _ VU _ _) _ _ = error $ "comp Kan: not implemented"
comp Pos i VU ts u = Kan i VU ts u

comp Pos i a ts u = error $
  "comp _: not implemented for " <+> show a <+> show ts <+> parens (show u)




-- -- -- Kan filling
-- fill :: Val -> Box Val -> Val
-- fill v box | isNeutralFill v box = VFillN v box
-- fill vid@(VId a v0 v1) box@(Box dir i v nvs) =
--   let x = fresh (vid, box)
--       box' = consBox (x,(v0,v1)) (mapBox (`appFormula` x) box)
--   in Path x $ fill (a `appFormula` x) box'
-- fill (VSigma a f) box@(Box dir x v nvs) =
--   let u = fill a (mapBox fstSVal box)
--   in VSPair u $ fill (app f u) (mapBox sndSVal box)
-- -- assumes cvs are constructor vals
-- fill v@(Ter (Sum _ nass) env) box@(Box _ _ (VCon n _) _) = case getIdent n nass of
--   Just as ->
--     let boxes = transposeBox $ mapBox unCon box
--     -- fill boxes for each argument position of the constructor
--     in VCon n $ fills as env boxes
--   Nothing -> error $ "fill: missing constructor in labelled sum " ++ n
-- fill (VEquivSquare x y a s t) box@(Box dir x' vx' nvs) =
--   VSquare x y $ fill a (modBox (unPack x y) box)
-- fill veq@(VEquivEq x a b f s t) box@(Box dir z vz nvs)
--   | x /= z && x `notElem` nonPrincipal box =
--     trace "VEquivEq case 1" $
--     let ax0 = fill a (mapBox fstVal box)
--         bx0 = app f ax0
--         bx  = mapBox sndVal box
--         bx' = mapBox (`face` (x,up)) bx
--         bx1 = fill b bx'        --- independent of x
--         v   = fill b $ (x,(bx0,bx1)) `consBox` bx
--     in VPair x ax0 v
--   | x /= z && x `elem` nonPrincipal box =
--     trace "VEquivEq case 2" $
--     let ax0 = lookBox (x,down) box

--         -- modification function
--         mf (ny,dy) vy | x /= ny    = sndVal vy
--                       | dy == down = app f ax0
--                       | otherwise  = vy

--         bx  = modBox mf box
--     in VPair x ax0 (fill b bx)
--   | x == z && dir == up =
--     trace "VEquivEq case 3" $
--     let ax0 = vz
--         bx0 = app f ax0
--         v   = fill b $ Box dir z bx0 [ (nnd,sndVal v) | (nnd,v) <- nvs ]
--     in VPair x ax0 v
--   | x == z && dir == down =
--     trace "VEquivEq case 4" $
--     let gbsb    = app s vz
--         (gb,sb) = (fstSVal gbsb, sndSVal gbsb)
--         y       = fresh (veq, box)
--         vy      = appFormula sb x

--         vpTSq :: Name -> Dir -> Val -> (Val,Val)
--         vpTSq nz dz (VPair z a0 v0) =
--           let vp       = VSPair a0 (Path z v0)
--               t0       = t `face` (nz,dz)
--               b0       = vz `face` (nz,dz)
--               l0sq0    = appFormula (app (app t0 b0) vp) y
--               (l0,sq0) = (fstSVal l0sq0, sndSVal l0sq0)
--               sq0x     = appFormula sq0 x
--           in (l0,sq0x)  -- TODO: check the correctness of the square s0

--         -- TODO: Use modBox!
--         vsqs   = [ ((n,d),vpTSq n d v) | ((n,d),v) <- nvs]
--         box1   = Box up y gb [ (nnd,v) | (nnd,(v,_)) <- vsqs ]
--         afill  = fill a box1
--         acom   = afill `face` (y,up)
--         fafill = app f afill
--         box2   = Box up y vy (((x,down),fafill) : ((x,up),vz) :
--                             [ (nnd,v) | (nnd,(_,v)) <- vsqs ])
--         bcom   = com b box2
--     in VPair x acom bcom
--   | otherwise = error "fill EqEquiv"
-- fill v@(Kan Com VU tbox') box@(Box dir x' vx' nvs')
--   | toAdd /= [] = -- W.l.o.g. assume that box contains faces for
--                   -- the non-principal sides of tbox.
--     trace "Kan Com 1" $
--     let -- TODO: Is this correct? Do we have to consider the auxsides?
--         add :: Side -> Val
--         add yc = let box' = mapBox (`face` yc) box
--                  in fill (lookBox yc tbox `face` (x,tdir)) box'

--         sides' = [ (n,(add (n,down),add (n,up))) | n <- toAdd ]

--      in fill v (sides' `appendBox` box)
--   | x' `notElem` nK =
--     trace "Kan Com 2" $
--     let principal    = fill tx (mapBox (pickout (x,tdir')) boxL)
--         nonprincipal =
--           [ let pyc  = principal `face` yc
--                 side = [((x,tdir),lookBox yc box),((x,tdir'),pyc)]
--                 v'   = fill (lookBox yc tbox)
--                             (side `appendSides` mapBox (pickout yc) boxL)
--                 in (yc,v')
--           | yc <- allDirs nK ]
--     in VComp (Box tdir x principal nonprincipal)
--   | x' `elem` nK =
--     trace "Kan Com 3" $
--     let -- assumes zc in defBox tbox
--         auxsides zc = [ (yd,pickout zc (lookBox yd box)) | yd <- allDirs nL ]

--         -- extend input box along x with orientation tdir'; results
--         -- in the non-principal faces on the intersection of defBox
--         -- box and defBox tbox; note, that the intersection contains
--         -- (x',dir'), but not (x',dir) (and (x,_))
--         npintbox = modBox (\yc boxside -> fill (lookBox yc tbox)
--                                           (Box tdir' x boxside (auxsides yc)))
--                      (subBox (nK `intersect` nJ) box)

--         npintfacebox = mapBox (`face` (x,tdir')) npintbox
--         principal    = fill tx (auxsides (x,tdir') `appendSides` npintfacebox)
--         nplp         = principal `face` (x',dir)
--         fnpintboxs   = [ (yc,v `face` (x',dir)) | (yc,v) <- sides npintbox ]
--         nplnp        = auxsides (x',dir) ++ fnpintboxs
--         -- the missing non-principal face on side (x',dir)
--         v'           = fill (lookBox (x',dir) tbox) (Box tdir x nplp nplnp)
--         nplast       = ((x',dir),v')

--     in VComp (Box tdir x principal (nplast:fromBox npintbox))
--   where nK    = nonPrincipal tbox
--         nJ    = nonPrincipal box
--         z     = fresh (tbox', box)
--         -- x is z
--         tbox@(Box tdir x tx nvs) = swap tbox' (pname tbox') z
--         toAdd = nK \\ (x' : nJ)
--         nL    = nJ \\ nK
--         boxL  = subBox nL box
--         dir'  = mirror dir
--         tdir' = mirror tdir
--         -- asumes zd is in the sides of tbox
--         pickout zd vcomp = lookBox zd (unCompAs vcomp z)
-- fill v@(Kan Fill VU tbox@(Box tdir x tx nvs)) box@(Box dir x' vx' nvs')
--   -- the cases should be (in order):
--   -- 1) W.l.o.g. K subset x', J
--   -- 2) x' = x &  dir = tdir
--   -- 3) x' = x &  dir = mirror tdir
--   -- 4) x' `notElem` K
--   -- 5) x' `elem` K
--   | toAdd /= [] =
--     -- W.l.o.g. x,nK subset x':nJ
--     trace "Kan Fill VU Case 1" $
--     let add :: Side -> Val
--         add zc = fill (v `face` zc) (mapBox (`face` zc) box)

--         newSides = [ (zc,add zc) | zc <- allDirs toAdd ]
--     in fill v (newSides `appendSides` box)
--   | x == x' && dir == tdir =
--     -- assumes K subset x',J
--     trace "Kan Fill VU Case 2" $
--     let boxp = lookBox (x,dir') box  -- is vx'
--         principal = fill (lookBox (x',tdir') tbox)
--                          (Box up z boxp (auxsides (x',tdir')))
--         nonprincipal =
--           [ (zc,let principzc = lookBox zc box
--                     fpzc = principal `face` zc
--                     -- "degenerate" along z!
--                     ppzc = principzc `face` (x,tdir)
--                     sides = [((x,tdir'),fpzc),((x,tdir),ppzc)]
--                 in fill (lookBox zc tbox)
--                         (Box up z principzc (sides ++ auxsides zc)))
--           | zc <- allDirs nK ]
--     in VFill z (Box tdir x principal nonprincipal)
--   | x == x' && dir == mirror tdir =
--     -- assumes K subset x',J
--     trace "Kan Fill VU Case 3" $
--     let -- the principal side of box must be a VComp
--         -- should be safe given the neutral test at the beginning
--         upperbox = unCompAs (lookBox (x,dir') box) x
--         nonprincipal =
--           [ (zc,let top    = lookBox zc upperbox
--                     bottom = lookBox zc box
--                     princ  = top `face` (x,tdir) -- same as: bottom `face` (x,tdir)
--                     sides  = [((z,down),bottom),((z,up),top)]
--                in fill (lookBox zc tbox) (Box tdir' x princ -- "degenerate" along z!
--                                        (sides ++ auxsides zc)))
--           | zc <- allDirs nK ]
--         nonprincipalfaces = [ (zc,u `face` (x,dir)) | (zc,u) <- nonprincipal ]
--         principal         = fill (lookBox (x,tdir') tbox)
--                              (Box up z (lookBox (x,tdir') upperbox)
--                                        (nonprincipalfaces ++ auxsides (x,tdir')))
--     in VFill z (Box tdir x principal nonprincipal)
--   | x' `notElem` nK =
--     -- assumes x,K subset x',J
--     trace "Kan Fill VU Case 4" $
--     let xaux      = unCompAs (lookBox (x,tdir) box) x
--         boxprinc  = unFillAs (lookBox (x',dir') box) z
--         princnp   = [((z,up),lookBox (x,tdir') xaux),
--                      ((z,down),lookBox (x,tdir') box)]
--                     ++ auxsides (x,tdir')
--         principal = fill (lookBox (x,tdir') tbox) -- tx
--                          (Box dir x' (lookBox (x,tdir') boxprinc) princnp)
--         nonprincipal = [ let yup  = lookBox yc xaux
--                              fyup = yup `face` (x,tdir)
--                              np   = [ ((z,up),yup), ((z,down),lookBox yc box)
--                                     , ((x,tdir), fyup) -- deg along z!
--                                     , ((x,tdir'), principal `face` yc) ]
--                                     ++ auxsides yc
--                              fb   = fill (lookBox yc tbox)
--                                          (Box dir x' (lookBox yc boxprinc) np)
--                          in (yc, fb)
--                        | yc <- allDirs nK]
--     in VFill z (Box tdir x principal nonprincipal)
--   | x' `elem` nK =
--     -- assumes x,K subset x',J
--     trace "Kan Fill VU Case 5" $
--     -- surprisingly close to the last case of the Kan-Com-VU filling
--     let upperbox = unCompAs (lookBox (x,dir') box) x
--         npintbox = modBox (\zc downside ->
--                             let bottom = lookBox zc box
--                                 top    = lookBox zc upperbox
--                                 princ  = downside
--                                          -- same as bottom `face` (x',tdir) and
--                                          -- top `face` (x',tdir)
--                                 sides  = [((z,down),bottom),((z,up),top)]
--                             in fill (lookBox zc tbox)
--                                     (Box tdir' x princ (sides ++ auxsides zc)))
--                    (subBox (nK `intersect` nJ) box)  -- intersection is nK - x'
--         npint = fromBox npintbox
--         npintfacebox = mapBox (`face` (x,tdir')) npintbox
--         principalbox = ([ ((z,down),lookBox (x,tdir') box)
--                         , ((z,up)  ,lookBox (x,tdir') upperbox)]
--                         ++ auxsides (x,tdir'))
--                        `appendSides` npintfacebox
--         principal = fill tx principalbox
--         nplp      = lookBox (x',dir) upperbox
--         nplnp = [ ((x,tdir), nplp `face` (x',dir)) -- deg along z!
--                 , ((x,tdir'),principal `face` (x',dir)) ]
--                 ++ auxsides (x',dir)
--                 ++ [ (zc,u `face` (x',dir)) | (zc,u) <- sides npintbox ]
--         fb = fill (lookBox (x',dir) tbox) (Box down z nplp nplnp)
--     in VFill z (Box tdir x principal (((x',dir),fb) : npint))
--     where z     = fresh (v, box)
--           nK    = nonPrincipal tbox
--           nJ    = nonPrincipal box
--           toAdd = (x:nK) \\ (x' : nJ)
--           nL    = nJ \\ (x : nK)
--           dir'  = mirror dir
--           tdir' = mirror tdir
--           -- asumes zc is in the sides of tbox
--           pickout zc vfill = lookBox zc (unFillAs vfill z)
--           -- asumes zc is in the sides of tbox
--           auxsides zc = [ (yd,pickout zc (lookBox yd box)) | yd <- allDirs nL ]
-- fill v b = Kan Fill v b

conv :: Int -> Val -> Val -> Bool
conv k VU VU                                  = True
conv k (Ter (Lam x u) e) (Ter (Lam x' u') e') =
  let v = mkVar k
  in conv (k+1) (eval (Pair e (x,v)) u) (eval (Pair e' (x',v)) u')
conv k (Ter (Lam x u) e) u' =
  let v = mkVar k
  in conv (k+1) (eval (Pair e (x,v)) u) (app u' v)
conv k u' (Ter (Lam x u) e) =
  let v = mkVar k
  in conv (k+1) (app u' v) (eval (Pair e (x,v)) u)
conv k (Ter (Split p _) e) (Ter (Split p' _) e') =
  (p == p') && convEnv k e e'
conv k (Ter (Sum p _) e)   (Ter (Sum p' _) e') =
  (p == p') && convEnv k e e'
conv k (Ter (PN (Undef p)) e) (Ter (PN (Undef p')) e') =
  (p == p') && convEnv k e e'
conv k (VPi u v) (VPi u' v') =
  let w = mkVar k
  in conv k u u' && conv (k+1) (app v w) (app v' w)
conv k (VId a u v) (VId a' u' v') = and [conv k a a', conv k u u', conv k v v']
conv k (Path i u) (Path i' u')    = trace "conv Path Path" $
                                    conv k (u `rename` (i,j)) (u' `rename` (i',j))
  where j = fresh (u,u')
conv k (Path i u) p'              = trace "conv Path p" $
                                    conv k (u `rename` (i,j)) (p' @@@ j)
  where j = fresh u
conv k p (Path i' u')             = trace "conv p Path" $
                                    conv k (p @@@ j) (u' `rename` (i',j))
  where j = fresh u'

conv k (VSigma u v) (VSigma u' v') = conv k u u' && conv (k+1) (app v w) (app v' w)
  where w = mkVar k
conv k (VFst u) (VFst u')              = conv k u u'
conv k (VSnd u) (VSnd u')              = conv k u u'
conv k (VSPair u v)   (VSPair u' v')   = conv k u u' && conv k v v'
conv k (VSPair u v)   w                =
  conv k u (fstSVal w) && conv k v (sndSVal w)
conv k w              (VSPair u v)     =
  conv k (fstSVal w) u && conv k (sndSVal w) v

conv k (VCon c us) (VCon c' us') = (c == c') && and (zipWith (conv k) us us')
conv k v@(Kan i a ts u) v'@(Kan i' a' ts' u') = trace "conv Kan" $
   let j    = fresh (v, v')
       tsj  = ts  `rename` (i,j)
       tsj' = ts' `rename` (i',j)
   in
   and [ conv k (a `rename` (i,j)) (a' `rename` (i',j))
       , Map.keysSet tsj == Map.keysSet tsj'
       , and $ Map.elems $ Map.intersectionWith (conv k) tsj tsj'
       , conv k (u `rename` (i,j)) (u' `rename` (i',j))]

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

conv k (VVar x)       (VVar x')        = (x == x')
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

convEnv :: Int -> Env -> Env -> Bool
convEnv k e e' = and $ zipWith (conv k) (valOfEnv e) (valOfEnv e')
