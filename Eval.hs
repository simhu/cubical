{-# LANGUAGE ParallelListComp #-}
module Eval where

import Control.Arrow (second)
import Data.List
import Data.Maybe (fromMaybe)
import Debug.Trace

import CTT

-- Switch to False to turn off debugging
debug :: Bool
debug = True

traceb :: String -> a -> a
traceb s x = if debug then trace s x else x

evals :: Env -> [(Binder,Ter)] -> [(Binder,Val)]
evals e = map (second (eval e))

unCompAs :: Val -> Name -> Box Val
unCompAs (VComp box) y = swap box (pname box) y
unCompAs v           _ = error $ "unCompAs: " ++ show v ++ " is not a VComp"

unFillAs :: Val -> Name -> Box Val
unFillAs (VFill x box) y = swap box x y
unFillAs v             _ = error $ "unFillAs: " ++ show v ++ " is not a VFill"

appName :: Val -> Name -> Val
appName (Path x u) y | y `elem` [0,1] = u `face` (x,y)
appName p y          | y `elem` [0,1] = VAppName p y		-- p has to be neutral
appName (Path x u) y                  =  -- swap u x y    -- assume that u is independent of y
 if x == y then u
   else if y `elem` support u
          then error ("appName " ++ "\nu = " ++ show u ++ "\ny = " ++ show y)
         else swap u x y
appName v y                           = -- traceb ("appName " ++ show v ++ "\ny = " ++ show y) $
 VAppName v y


-- p(x) = <z>q(x,z)
-- a(x) = q(x,0)     b(x) = q(x,1)
-- q(0,y) connects a(0) and b(0)
-- we connect q(0,0) to q(1,1)
-- appDiag :: Val -> Val -> Name -> Val
-- appDiag tu p x | x `elem` [0,1] = appName p x
-- appDiag tu p x =
-- -- traceb ("appDiag " ++ "\ntu = " ++ show tu ++ "\np = " ++ show p ++ "\nx = "
-- --                       ++ show x ++ " " ++ show y
-- --                       ++ "\nq = " ++ show q) -- "\nnewBox =" ++ show newBox)
--  com tu newBox
--    where y = fresh (p,(tu,x))
--          q = appName p y
--          a = appName p 0
--          b = appName p 1
--          newBox = Box down y b [((x,down),q `face` (x,down)),((x,up),b `face` (x,up))]


-- Compute the face of a value
face :: Val -> Side -> Val
face u xdir@(x,dir) =
  let fc v = v `face` xdir in case u of
  VU          -> VU
  Ter t e     -> eval (e `faceEnv` xdir) t
  VId a v0 v1 -> VId (fc a) (fc v0) (fc v1)
  Path y v | x == y    -> u
           | otherwise -> Path y (fc v)
  VExt y b f g p | x == y && dir == down -> f
                 | x == y && dir == up   -> g
                 | otherwise             -> VExt y (fc b) (fc f) (fc g) (fc p)
  VPi a f    -> VPi (fc a) (fc f)
  VSigma a f -> VSigma (fc a) (fc f)
  VSPair a b -> VSPair (fc a) (fc b)
  VInh v     -> VInh (fc v)
  VInc v     -> VInc (fc v)
  VSquash y v0 v1 | x == y && dir == down -> v0
                  | x == y && dir == up   -> v1
                  | otherwise             -> VSquash y (fc v0) (fc v1)
  VCon c us -> VCon c (map fc us)
  VEquivEq y a b f s t | x == y && dir == down -> a
                       | x == y && dir == up   -> b
                       | otherwise             ->
                         VEquivEq y (fc a) (fc b) (fc f) (fc s) (fc t)
  VPair y a v | x == y && dir == down -> a
              | x == y && dir == up   -> fc v
              | otherwise             -> VPair y (fc a) (fc v)
  VEquivSquare y z a s t | x == y                -> a
                         | x == z && dir == down -> a
                         | x == z && dir == up   -> VEquivEq y a a idV s t
                         | otherwise             ->
                          VEquivSquare y z (fc a) (fc s) (fc t)
  VSquare y z v | x == y                -> fc v
                | x == z && dir == down -> fc v
                | x == z && dir == up   -> idVPair y (fc v)
                | otherwise             -> VSquare y z (fc v)
  Kan Fill a b@(Box dir' y v nvs)
    | x /= y && x `notElem` nonPrincipal b -> fill (fc a) (mapBox fc b)
    | x `elem` nonPrincipal b              -> lookBox (x,dir) b
    | x == y && dir == mirror dir'         -> v
    | otherwise                            -> com a b
  VFillN a b@(Box dir' y v nvs)
    | x /= y && x `notElem` nonPrincipal b -> fill (fc a) (mapBox fc b)
    | x `elem` nonPrincipal b              -> lookBox (x,dir) b
    | x == y && dir == mirror dir'         -> v
    | otherwise                            -> com a b
  Kan Com a b@(Box dir' y v nvs)
    | x == y                     -> u
    | x `notElem` nonPrincipal b -> com (fc a) (mapBox fc b)
    | x `elem` nonPrincipal b    -> lookBox (x,dir) b `face` (y,dir')
  VComN a b@(Box dir' y v nvs)
    | x == y                     -> u
    | x `notElem` nonPrincipal b -> com (fc a) (mapBox fc b)
    | x `elem` nonPrincipal b    -> lookBox (x,dir) b `face` (y,dir')
  VComp b@(Box dir' y _ _)
    | x == y                     -> u
    | x `notElem` nonPrincipal b -> VComp (mapBox fc b)
    | x `elem` nonPrincipal b    -> lookBox (x,dir) b `face` (y,dir')
  VFill z b@(Box dir' y v nvs)
    | x == z                               -> u
    | x /= y && x `notElem` nonPrincipal b -> VFill z (mapBox fc b)
    | (x,dir) `elem` defBox b              ->
      lookBox (x,dir) (mapBox (`face` (z,down)) b)
    | x == y && dir == dir'                ->
        VComp $ mapBox (`face` (z,up)) b
  VInhRec b p h a -> inhrec (fc b) (fc p) (fc h) (fc a)
  VApp u v        -> app (fc u) (fc v)
  VAppName u n    -> traceb ("face " ++ "\nxdir " ++ show xdir ++
                             "\nu " ++ show u ++ "\nn " ++ show n) $
                      appName (fc u) (faceName n xdir)
  VSplit u v      -> app (fc u) (fc v)
  VVar s d        -> VVar s [faceName n xdir | n <- d]
  VFst p          -> fstSVal (fc p)
  VSnd p          -> sndSVal (fc p)
  VCircle         -> VCircle
  VBase           -> VBase
  VLoop y
    | x == y    -> VBase
    | otherwise -> VLoop y
  VCircleRec f b l s -> circlerec (fc f) (fc b) (fc l) (fc s)
  VI  -> VI
  VI0 -> VI0
  VI1 -> VI1
  VLine y
    | x == y && dir == down -> VI0
    | x == y && dir == up   -> VI1
    | otherwise             -> VLine y
  VIntRec f s e l u -> intrec (fc f) (fc s) (fc e) (fc l) (fc u)


faceName :: Name -> Side -> Name
faceName 0 _                 = 0
faceName 1 _                 = 1
faceName x (y,d) | x == y    = d
                 | otherwise = x

idV :: Val
idV = Ter (Lam "x" (Var "x")) Empty

idVPair :: Name -> Val -> Val
idVPair x v = VPair x (v `face` (x,down)) v

-- Compute the face of an environment
faceEnv :: Env -> Side -> Env
faceEnv e xd = mapEnv (`face` xd) e

look :: Binder -> Env -> Val
look x (Pair s (y,u)) | x == y    = u
                      | otherwise = look x s
look x r@(PDef es r1)             = look x (upds r1 (evals r es))

cubeToBox :: Val -> Box () -> Box Val
cubeToBox v = modBox (\nd _ -> v `face` nd)

evalAppPN :: Env -> PN -> [Ter] -> Val
evalAppPN e pn ts
  | length ts < arity pn =
      let r       = arity pn - length ts
          binders = map (\n -> '_' : show n) [1..r]
          vars    = map Var binders
      in Ter (mkLams binders $ mkApps (PN pn) (ts ++ vars)) e
      -- in mkLams binders $ evalPN e pn (ts ++ vars)
  | otherwise            =
      let (args,rest) = splitAt (arity pn) ts
      in apps (evalPN (freshs e) pn (map (eval e) args)) (map (eval e) rest)

evalPN :: [Name] -> PN -> [Val] -> Val
evalPN (x:_) Id            [a,a0,a1]     = VId (Path x a) a0 a1
evalPN (x:_) IdP           [_,_,p,a0,a1] = VId p a0 a1
evalPN (x:_) Refl          [_,a]         = Path x a
evalPN (x:_) TransU        [_,_,p,t]     = com (appName p x) $ Box up x t []
evalPN (x:_) TransInvU     [_,_,p,t]     = com (appName p x) $ Box down x t []
evalPN (x:_) TransURef     [a,t]         = Path x $ fill a $ Box up x t []
evalPN (x:_) TransUEquivEq [_,b,f,_,_,u] = Path x (fill b box)
  where box = Box up x (app f u) []   -- TODO: Check this!
evalPN (x:y:_) CSingl [a,u,v,p] = Path x (VSPair omega (Path y theta))
 where pv = appName p y
       theta = fill a (Box up y u [((x,down),u),((x,up),pv)])
       omega = theta `face` (y,up)
evalPN (x:_)   Ext        [_,b,f,g,p]   = Path x $ VExt x b f g p
evalPN _       Inh        [a]           = VInh a
evalPN _       Inc        [_,t]         = VInc t
evalPN (x:_)   Squash     [_,r,s]       = Path x $ VSquash x r s
evalPN _       InhRec     [_,b,p,phi,a] = inhrec b p phi a
evalPN (x:_)   EquivEq    [a,b,f,s,t]   = Path x $ VEquivEq x a b f s t
evalPN (x:y:_) EquivEqRef [a,s,t]       =
  Path y $ Path x $ VEquivSquare x y a s t
evalPN (x:_)   MapOnPath  [_,_,f,_,_,p]    = Path x $ app f (appName p x)
evalPN (x:_)   MapOnPathD [_,_,f,_,_,p]    = Path x $ app f (appName p x)
evalPN (x:_)   AppOnPath [_,_,_,_,_,_,p,q] = Path x $ app (appName p x) (appName q x)
evalPN (x:_)   MapOnPathS [_,_,_,f,_,_,p,_,_,q] = Path x $ app (app f (appName p x)) (appName q x)
evalPN _       Circle     []               = VCircle
evalPN _       Base       []               = VBase
evalPN (x:_)   Loop       []               = Path x $ VLoop x
evalPN _       CircleRec  [f,b,l,s]        = circlerec f b l s
evalPN _       I          []               = VI
evalPN _       I0         []               = VI0
evalPN _       I1         []               = VI1
evalPN (x:_)   Line       []               = Path x $ VLine x
evalPN _       IntRec     [f,s,e,l,u]      = intrec f s e l u
evalPN _       u _ = error ("evalPN " ++ show u)


eval :: Env -> Ter -> Val
eval _ U             = VU
eval e (PN pn)       = evalAppPN e pn []
eval e t@(App r s) =
  let (u,us) = unApps t
  in case u of
       PN pn -> evalAppPN e pn us
       _     -> app (eval e r) (eval e s)
eval e (Var i)       = look i e
eval e (Pi a b)      = VPi (eval e a) (eval e b)
eval e (Lam x t)     = Ter (Lam x t) e -- stop at lambdas
eval e (Sigma a b)   = VSigma (eval e a) (eval e b)
eval e (SPair a b)   = VSPair (eval e a) (eval e b)
eval e (Fst a)       = fstSVal (eval e a)
eval e (Snd a)       = sndSVal (eval e a)
eval e (Where t (_,def))       = eval (PDef def e) t
eval e (Con name ts)       = VCon name (map (eval e) ts)
eval e (Split pr alts)     = Ter (Split pr alts) e
eval e (Sum pr ntss)      = Ter (Sum pr ntss) e

inhrec :: Val -> Val -> Val -> Val -> Val
inhrec _ _ phi (VInc a)          = app phi a
inhrec b p phi (VSquash x a0 a1) = appName (face (app (app p b0) b1) (x,down)) x
  -- appDiag b (app (app p b0) b1) x  -- x may occur in p and/or b
  where fc w d = w `face` (x,d)
        b0     = inhrec (fc b down) (fc p down) (fc phi down) a0
        b1     = inhrec (fc b up)   (fc p up)   (fc phi up)   a1
inhrec b p phi (Kan ktype (VInh a) box) =
  kan ktype b (modBox irec box)
    where irec (j,dir) v = let fc v = v `face` (j,dir)
                           in inhrec (fc b) (fc p) (fc phi) v
inhrec b p phi v = VInhRec b p phi v -- v should be neutral

circlerec :: Val -> Val -> Val -> Val -> Val
circlerec _ b _ VBase = b
circlerec f b l v@(VLoop x) =
 traceb ("circlerec " ++ "\nf = " ++ show f ++ "\nl = " ++ show l ++ "\nx = " ++ show x)
--        $ appDiag (app f v) l x
 com a (Box down y px1 [((x,down),p0y),((x,up),p11)])
 where y     = fresh [f,b,l,v]
       pxy   = appName l y
       theta = connection VCircle x y v
       a     = app f theta
       px1   = pxy `face` (y,up)
       p11   = px1 `face` (x,up)
       p0y   = pxy `face` (x,down)
circlerec f b l v@(Kan ktype VCircle box) =
  kan ktype (app f v) (modBox crec box)
  where crec side u = let fc w = w `face` side
                      in circlerec (fc f) (fc b) (fc l) u
circlerec f b l v = VCircleRec f b l v -- v should be neutral

-- Assumes y is fresh and x fresh for a; constructs a connection
-- square with faces u (x), u (y), u (1), u (1).
connection :: Val -> Name -> Name -> Val -> Val
connection a x y u =
  let u1 = u `face` (x,up)
      ufill = fill a (Box down y u1 [((x,down), swap u x y), ((x,up),u1)])
      z = fresh ([x,y], [a,u])
      ufillzy = swap ufill x z
      ufillzx = swap ufillzy y x
  in
   com a (Box down z u1
          [((x,down),ufillzy),((x,up),u1),((y,down),ufillzx),((y,up),u1)])

intrec :: Val -> Val -> Val -> Val -> Val -> Val
intrec _ s _ _ VI0         = s
intrec _ _ e _ VI1         = e
intrec f s e l v@(VLine x) =
  com a (Box down y px1 [((x,down),p0y),((x,up),p11)])
  where y = fresh [f,s,e,l,v]
        pxy   = appName l y
        theta = connection VI x y v
        a     = app f theta
        px1   = pxy `face` (y,up)
        p11   = px1 `face` (x,up)
        p0y   = pxy `face` (x,down)
intrec f s e l v@(Kan ktype VCircle box) =
  kan ktype (app f v) (modBox irec box)
  where irec side u = let fc w = w `face` side
                      in intrec (fc f) (fc s) (fc e) (fc l) u
intrec f s e l v = VIntRec f s e l v -- v should be neutral

fstSVal :: Val -> Val
fstSVal (VSPair a b) = a
fstSVal u | isNeutral u = VFst u
          | otherwise   = error $ show u ++ " should be neutral"
sndSVal :: Val -> Val
sndSVal (VSPair a b) = b
sndSVal u | isNeutral u = VSnd u
          | otherwise   = error $ show u ++ " should be neutral"

kan :: KanType -> Val -> Box Val -> Val
kan Fill = fill
kan Com  = com

isNeutralFill :: Val -> Box Val -> Bool
isNeutralFill v box | isNeutral v = True
isNeutralFill v@(Ter (PN (Undef _)) _) box = True
isNeutralFill veq@(VEquivEq x a b f s t) box@(Box dir z vz nvs)
--  | x == z && dir == down && not (isCon (app s vz)) = True
  | x == z && dir == down && isNeutral (app s vz) = True
isNeutralFill v@(Kan Com VU tbox') box@(Box d x _ _) =
--  not (and [isVComp (lookBox yc box) | yc <- aDs])
  or [isNeutral (lookBox yc box) | yc <- aDs]
   where
        nK    = nonPrincipal tbox'
        nJ    = nonPrincipal box
        nL    = nJ \\ nK
        aDs   = if x `elem` nK then allDirs nL else (x,mirror d):(allDirs nL)
isNeutralFill v@(Kan Fill VU tbox') box@(Box d x _ _) =
--  not (and [isVFill (lookBox yc box) | yc <- aDs])
  or [isNeutral (lookBox yc box) | yc <- aDs]
   where
        nK    = (pname tbox'):(nonPrincipal tbox')
        nJ    = nonPrincipal box
        nL    = nJ \\ nK
        aDs   = if x `elem` nK then allDirs nL else (x,mirror d):(allDirs nL)
isNeutralFill v@(VEquivEq z a b f s t) box@(Box d x _ _) =
--  not (and [isVPair (lookBox yc box) | yc <- aDs])
-- TODO: check
  or [isNeutral (lookBox yc box) | yc <- aDs]
   where
        nJ    = nonPrincipal box
        nL    = nJ \\ [z]
        aDs   = if x == z then allDirs nL else (x,mirror d):(allDirs nL)
isNeutralFill v@(VEquivSquare y z _ _ _) box@(Box d x _ _) =
--  not (and [isVSquare (lookBox yc box) | yc <- aDs])
  or [isNeutral (lookBox yc box) | yc <- aDs]
   where
        nJ    = nonPrincipal box
        nL    = nJ \\ [y,z]
        aDs   = if x `elem` [y,z] then allDirs nL else (x,mirror d):(allDirs nL)
isNeutralFill (Ter (Sum _ _) _) (Box _ _ v nvs) =
-- not (and ((isCon v):[isCon u | (_,u) <- nvs]))
 or ((isNeutral v):[isNeutral u | (_,u) <- nvs])
isNeutralFill v box = False

-- Kan filling
fill :: Val -> Box Val -> Val
fill v box | isNeutralFill v box = VFillN v box
fill vid@(VId a v0 v1) box@(Box dir i v nvs) = Path x $ fill (a `appName` x) box'
  where x    = fresh (vid, box)
        box' = (x,(v0,v1)) `consBox` mapBox (`appName` x) box
fill (VSigma a f) box@(Box dir x v nvs) =
  VSPair u $ fill (app f u) (mapBox sndSVal box)
    where u = fill a (mapBox fstSVal box)
-- assumes cvs are constructor vals
fill v@(Ter (Sum _ nass) env) box@(Box _ _ (VCon n _) _)  =
 VCon n ws
  where as = case lookup n nass of
               Just as -> as
               Nothing -> error $ "fill: missing constructor "
                               ++ "in labelled sum " ++ n
        boxes = transposeBox $ mapBox unCon box
        -- fill boxes for each argument position of the constructor
        ws    = fills as env boxes
fill (VEquivSquare x y a s t) box@(Box dir x' vx' nvs) =
  VSquare x y v
  where v = fill a $ modBox unPack box
        unPack :: (Name,Dir) -> Val -> Val
        unPack (z,c) v | z /= x && z /= y  = unSquare v
                       | z == y && c == up = sndVal v
                       | otherwise         = v

fill veq@(VEquivEq x a b f s t) box@(Box dir z vz nvs)
  | x /= z && x `notElem` nonPrincipal box =
    let ax0  = fill a (mapBox fstVal box)
        bx0  = app f ax0
        bx   = mapBox sndVal box
        bx1  = fill b $ mapBox (`face` (x,up)) bx       --- independent of x
        v    = fill b $ (x,(bx0,bx1)) `consBox` bx
    in traceb ("VEquivEq case 1" ) $ VPair x ax0 v
  | x /= z && x `elem` nonPrincipal box =
    let ax0 = lookBox (x,down) box
        bx  = modBox (\(ny,dy) vy -> if x /= ny then sndVal vy else
                                       if dy == down then app f ax0 else vy) box
        v   = fill b bx
    in traceb "VEquivEq case 2" $ VPair x ax0 v
  | x == z && dir == up =
    let ax0  = vz
        bx0  = app f ax0
        v    = fill b $ Box dir z bx0 [ (nnd,sndVal v) | (nnd,v) <- nvs ]
    in traceb "VEquivEq case 3" $ VPair x ax0 v
  | x == z && dir == down =
        let gbsb = app s vz
            (gb,sb)  = (fstSVal gbsb, sndSVal gbsb)
            y  = fresh (veq, box)
            vy = appName sb x

            vpTSq :: Name -> Dir -> Val -> (Val,Val)
            vpTSq nz dz (VPair z a0 v0) =
             let vp = VSPair a0 (Path z v0)
                 t0 = t `face` (nz,dz)
                 b0 = vz `face` (nz,dz)
                 l0sq0 = appName (app (app t0 b0) vp) y
                 (l0,sq0) = (fstSVal l0sq0, sndSVal l0sq0)
             in (l0,appName sq0 x)  -- TODO: check the correctness of the square s0

         -- TODO: Use modBox!
            vsqs   = [ ((n,d),vpTSq n d v) | ((n,d),v) <- nvs]
            box1   = Box up y gb [ (nnd,v) | (nnd,(v,_)) <- vsqs ]
            afill  = fill a box1

            acom   = afill `face` (y,up)
            fafill = app f afill
            box2   = Box up y vy (((x,down),fafill) : ((x,up),vz) :
                                      [ (nnd,v) | (nnd,(_,v)) <- vsqs ])
            bcom   = com b box2
        in traceb "VEquivEq case 4" $ VPair x acom bcom
  | otherwise = error "fill EqEquiv"


fill v@(Kan Com VU tbox') box@(Box dir x' vx' nvs')
  | toAdd /= [] = -- W.l.o.g. assume that box contains faces for
    let           -- the non-principal sides of tbox.
      add :: Side -> Val  -- TODO: Is this correct? Do we have
                          -- to consider the auxsides?
      add yc = fill (lookBox yc tbox `face` (x,tdir)) (mapBox (`face` yc) box)
      newBox = [ (n,(add (n,down),add (n,up)))| n <- toAdd ] `appendBox` box
    in fill v newBox
  | x' `notElem` nK =
    let principal = fill tx (mapBox (pickout (x,tdir')) boxL)
        nonprincipal =
          [ let side = [((x,tdir),lookBox yc box)
                       ,((x,tdir'),principal `face` yc)]
            in (yc, fill (lookBox yc tbox)
                    (side `appendSides` mapBox (pickout yc) boxL))
          | yc <- allDirs nK ]
        newBox = Box tdir x principal nonprincipal
    in traceb ("Kan Com 2 ") VComp newBox
  | x' `elem` nK =
    let -- assumes zc in defBox tbox
      auxsides zc = [ (yd,pickout zc (lookBox yd box)) | yd <- allDirs nL ]
      -- extend input box along x with orientation tdir'; results
      -- in the non-principal faces on the intersection of defBox
      -- box and defBox tbox; note, that the intersection contains
      -- (x',dir'), but not (x',dir) (and (x,_))
      npintbox = modBox (\yc boxside -> fill (lookBox yc tbox)
                                  (Box tdir' x boxside (auxsides yc)))
                        (subBox (nK `intersect` nJ) box)
      npint = fromBox npintbox
      npintfacebox = mapBox (`face` (x,tdir')) npintbox
      principal = fill tx (auxsides (x,tdir') `appendSides` npintfacebox)
      nplp  = principal `face` (x',dir)
      nplnp = auxsides (x',dir)
              ++ map (\(yc,v) -> (yc,v `face` (x',dir))) (sides npintbox)
      -- the missing non-principal face on side (x',dir)
      nplast = ((x',dir),fill (lookBox (x',dir) tbox) (Box tdir x nplp nplnp))
      newBox = Box tdir x principal (nplast:npint)
    in traceb ("Kan Com 3 ") $ VComp newBox
 -- ++ "\nnpintbox = " ++ showBox npintbox
 --               ++ "\nxtdir' = " ++ show (x,tdir'))
  where nK    = nonPrincipal tbox
        nJ    = nonPrincipal box
        z     = fresh (tbox', box)
        -- x is z
        tbox@(Box tdir x tx nvs) = swap tbox' (pname tbox') z
        toAdd = nK \\ (x' : nJ)
        nL    = nJ \\ nK
        boxL  = subBox nL box
        dir'  = mirror dir
        tdir' = mirror tdir
        -- asumes zd is in the sides of tbox
        pickout zd vcomp = lookBox zd (unCompAs vcomp z)

fill v@(Kan Fill VU tbox@(Box tdir x tx nvs)) box@(Box dir x' vx' nvs')
  -- the cases should be (in order):
  -- 1) W.l.o.g. K subset x', J
  -- 2) x' = x &  dir = tdir
  -- 3) x' = x &  dir = mirror tdir
  -- 4) x `notElem` J (maybe combine with 1?)
  -- 5) x' `notElem` K
  -- 6) x' `elem` K
  | toAdd /= [] =
    let
      add :: Side -> Val
      add zc = fill (lookBox zc tbox) (mapBox (`face` zc) box)
      newBox = [ (zc,add zc) | zc <- allDirs toAdd ] `appendSides` box
    in traceb "Kan Fill VU Case 1" fill v newBox            -- W.l.o.g. nK subset x:nJ
  | x == x' && dir == tdir = -- assumes K subset x',J
    let
      boxp = lookBox (x,dir') box  -- is vx'
      principal = fill (lookBox (x',tdir') tbox) (Box up z boxp (auxsides (x',tdir')))
      nonprincipal =
        [ (zc,
           let principzc = lookBox zc box
               sides = [((x,tdir'),principal `face` zc)
                       ,((x,tdir),principzc)] -- "degenerate" along z!
           in fill (lookBox zc tbox) (Box up z principzc (sides ++ auxsides zc)))
        | zc <- allDirs nK ]
    in     traceb ("Kan Fill VU Case 2") --  ++ show v ++ "\nbox= " ++ show box
     VFill z (Box tdir x' principal nonprincipal)

  | x == x' && dir == mirror tdir = -- assumes K subset x',J
        let      -- the principal side of box must be a VComp
          upperbox = unCompAs (lookBox (x,dir') box) x   -- should be safe given the neutral test at the beginning
          nonprincipal =
            [ (zc,
               let top    = lookBox zc upperbox
                   bottom = lookBox zc box
                   princ  = top `face` (x',tdir) -- same as: bottom `face` (x',tdir)
                   sides  = [((z,down),bottom),((z,up),top)]
               in fill (lookBox zc tbox)
                    (Box tdir' x princ -- "degenerate" along z!
                     (sides ++ auxsides zc)))
            | zc <- allDirs nK ]
          nonprincipalfaces =
            map (\(zc,u) -> (zc,u `face` (x,dir))) nonprincipal
          principal =
            fill (lookBox (x,tdir') tbox) (Box up z (lookBox (x,tdir') upperbox)
                                         (nonprincipalfaces ++ auxsides (x,tdir')))
        in traceb "Kan Fill VU Case 3"
           VFill z (Box tdir x' principal nonprincipal)
  | x `notElem` nJ =  -- assume x /= x' and K subset x', J
    let
      comU   = v `face` (x,tdir) -- Kan Com VU (tbox (z=up))
      xsides = [((x,tdir), fill comU (mapBox (`face` (x,tdir)) box))
               ,((x,tdir'),fill (lookBox (x,tdir') tbox)
                            (mapBox (`face` (x,tdir)) box))]
    in       traceb "Kan Fill VU Case 4"
     fill v (xsides `appendSides` box)
  | x' `notElem` nK =  -- assumes x,K subset x',J
        let
          xaux      = unCompAs (lookBox (x,tdir) box) x -- TODO: Do we need a fresh name?
          boxprinc  = unFillAs (lookBox (x',dir') box) z
          princnp   = [((z,up),lookBox (x,tdir') xaux)
                      ,((z,down),lookBox (x,tdir') box)]
                      ++ auxsides (x,tdir')
          principal = fill (lookBox (x,tdir') tbox) -- tx
                        (Box dir x' (lookBox (x,tdir') boxprinc) princnp)
          nonprincipal =
            [ let yup = lookBox yc xaux
                  np  = [((z,up),yup),((z,down),lookBox yc box)
                        ,((y,c), yup `face` (x,tdir)) -- deg along z!
                        ,((y,mirror c), principal `face` yc)]
                        ++ auxsides yc
              in (yc, fill (lookBox yc tbox)
                        (Box dir x' (lookBox yc boxprinc) np))
            | yc@(y,c) <- allDirs nK]
        in     traceb "Kan Fill VU Case 5"
               VFill z (Box tdir x' principal nonprincipal)
  | x' `elem` nK =              -- assumes x,K subset x',J
        let -- surprisingly close to the last case of the Kan-Com-VU filling
          upperbox = unCompAs (lookBox (x,dir') box) x
          npintbox =
            modBox (\zc downside ->
                     let bottom = lookBox zc box
                         top    = lookBox zc upperbox
                         princ  = downside -- same as bottom `face` (x',tdir) and
                                           -- top `face` (x',tdir)
                         sides  = [((z,down),bottom),((z,up),top)]
                     in fill (lookBox zc tbox) (Box tdir' x princ -- deg along z!
                                                (sides ++ auxsides zc)))
                   (subBox (nK `intersect` nJ) box)
          npint = fromBox npintbox
          npintfacebox = mapBox (`face` (x,tdir)) npintbox
          principalbox = ([((z,down),lookBox (x,tdir') box)
                         ,((z,up)  ,lookBox (x,tdir')upperbox)] ++
                         auxsides (x,tdir')) `appendSides` npintfacebox
          principal = fill tx principalbox
          nplp   = lookBox (x',dir) upperbox
          nplnp  = [((x',dir), nplp `face` (x',dir)) -- deg along z!
                   ,((x', dir'),principal `face` (x',dir))]
                   ++ auxsides (x',dir)
                   ++ map (\(zc,u) -> (zc,u `face` (x',dir))) (sides npintbox)
          nplast = ((x',dir),fill (lookBox (x',dir) tbox) (Box down z nplp nplnp))
        in       traceb "Kan Fill VU Case 6"
         VFill z (Box tdir x' principal (nplast:npint))
    where z     = fresh (v, box)
          nK    = nonPrincipal tbox
          nJ    = nonPrincipal box
          toAdd = nK \\ (x' : nJ)
          nL    = nJ \\ nK
          boxL  = subBox nL box
          dir'  = mirror dir
          tdir' = mirror tdir
          -- asumes zc is in the sides of tbox
          pickout zc vfill = lookBox zc (unFillAs vfill z)
          -- asumes zc is in the sides of tbox
          auxsides zc = [ (yd,pickout zc (lookBox yd box)) | yd <- allDirs nL ]

fill v b = Kan Fill v b

fills :: [(Binder,Ter)] -> Env -> [Box Val] -> [Val]
fills []         _ []          = []
fills ((x,a):as) e (box:boxes) = v : fills as (Pair e (x,v)) boxes
  where v = fill (eval e a) box
fills _ _ _ = error "fills: different lengths of types and values"

-- Composition (ie., the face of fill which is created)
com :: Val -> Box Val -> Val
com u box | isNeutralFill u box = VComN u box
com vid@VId{} box@(Box dir i _ _)         = fill vid box `face` (i,dir)
com vsigma@VSigma{} box@(Box dir i _ _)   = fill vsigma box `face` (i,dir)
com veq@VEquivEq{} box@(Box dir i _ _)    = fill veq box `face` (i,dir)
com u@(Kan Com VU _) box@(Box dir i _ _)  = fill u box `face` (i,dir)
com u@(Kan Fill VU _) box@(Box dir i _ _) = fill u box `face` (i,dir)
com ter@Ter{} box@(Box dir i _ _)         = fill ter box `face` (i,dir)
com v box                                 = Kan Com v box
 -- traceb ("com " ++ "\nv = " ++ show v ++ "\n box = " ++ show box) (Kan Com v box)

appBox :: Box Val -> Box Val -> Box Val
appBox (Box dir x v nvs) (Box _ _ u nus) = Box dir x (app v u) nvus
  where nvus      = [ (nnd,app v (lookup' nnd nus)) | (nnd,v) <- nvs ]
        lookup' x = fromMaybe (error "appBox") . lookup x

app :: Val -> Val -> Val
app (Ter (Lam x t) e) u                         = eval (Pair e (x,u)) t
app (Kan Com (VPi a b) box@(Box dir x v nvs)) u =
  traceb ("Pi Com ")
  com (app b ufill) (appBox box bcu)
  where ufill = fill a (Box (mirror dir) x u [])
        bcu   = cubeToBox ufill (shapeOfBox box)
app kf@(Kan Fill (VPi a b) box@(Box dir i w nws)) v =
  traceb ("Pi fill ") $ answer
  where x     = fresh (kf, v)
        u     = v `face` (i,dir)
        ufill = fill a (Box (mirror dir) i u [])
        bcu   = cubeToBox ufill (shapeOfBox box)
        vfill = fill a (Box (mirror dir) i u [((x,down),ufill),((x,up),v)])
        vx    = fill (app b ufill) (appBox box bcu)
        vi0   = app w (vfill `face` (i,down))
        vi1   = com (app b ufill) (appBox box bcu)
        nvs   = [ ((n,d),app ws (vfill `face` (n,d))) | ((n,d),ws) <- nws ]
        answer = com (app b vfill) (Box up x vx (((i,down),vi0) : ((i,up),vi1):nvs))
app vext@(VExt x bv fv gv pv) w = com (app bv w) (Box up y pvxw [((x,down),left),((x,up),right)])
  -- NB: there are various choices how to construct this
  where y     = fresh (vext, w)
        w0    = w `face` (x,down)
        left  = app fv w0
        right = app gv (swap w x y)
        pvxw  = appName (app pv w0) x
app (Ter (Split _ nvs) e) (VCon name us) = case lookup name nvs of
    Just (xs,t)  -> eval (upds e (zip xs us)) t
    Nothing -> error $ "app: Split with insufficient "
               ++ "arguments; missing case for " ++ name
app u@(Ter (Split _ _) _) v  -- = VSplit u v -- v should be neutral
           | isNeutral v = VSplit u v
           | otherwise   = error $ "app: (VSplit) " ++ show v ++ " is not neutral"
app r s                      --  = VApp r s -- r should be neutral
           | isNeutral r = VApp r s -- r should be neutral
           | otherwise   = error $ "app: (VApp) " ++ show r ++ " is not neutral"

apps :: Val -> [Val] -> Val
apps = foldl app

convBox :: Int -> Box Val -> Box Val -> Bool
convBox k box@(Box d pn _ ss) box'@(Box d' pn' _ ss') =
  if   and [d == d', pn == pn', sort np == sort np']
  then and [conv1 k (lookBox s box) (lookBox s box') | s <- defBox box]
  else False
  where (np, np') = (nonPrincipal box, nonPrincipal box')

conv1 :: Int -> Val -> Val -> Bool
conv1 k u v = -- traceb (show ("\n" ++ " =? "))
              -- traceb (show u ++ " =? " ++ show v ++ "\n")
              (conv k u v)

conv :: Int -> Val -> Val -> Bool
conv k VU VU                 = True
conv k (Ter (Lam x u) e) (Ter (Lam x' u') e') =
    conv1 (k+1) (eval (Pair e (x,v)) u) (eval (Pair e' (x',v)) u')
    where v = mkVar k $ support (e, e')
conv k (Ter (Lam x u) e) u' = conv1 (k+1) (eval (Pair e (x,v)) u) (app u' v)
    where v = mkVar k $ support e
conv k u' (Ter (Lam x u) e) = conv1 (k+1) (app u' v) (eval (Pair e (x,v)) u)
    where v = mkVar k $ support e
conv k (Ter (Split p _) e) (Ter (Split p' _) e') = (p == p') && convEnv k e e'
conv k (Ter (Sum p _) e)   (Ter (Sum p' _) e')   = (p == p') && convEnv k e e'
conv k (Ter (PN (Undef p)) e) (Ter (PN (Undef p')) e') = (p == p') && convEnv k e e'
conv k (VPi u v) (VPi u' v') = conv1 k u u' && conv1 (k+1) (app v w) (app v' w)
    where w = mkVar k $ support [u,u',v,v']
conv k (VSigma u v) (VSigma u' v') = conv1 k u u' && conv1 (k+1) (app v w) (app v' w)
    where w = mkVar k $ support [u,u',v,v']
conv k (VId a u v) (VId a' u' v') = and [conv1 k a a', conv1 k u u', conv1 k v v']
conv k (Path x u) (Path x' u')    = conv1 k (swap u x z) (swap u' x' z)
  where z = fresh (u,u')
conv k (Path x u) p'              = conv1 k (swap u x z) (appName p' z)
  where z = fresh u
conv k p (Path x' u')             = conv1 k (appName p z) (swap u' x' z)
  where z = fresh u'
conv k (VExt x b f g p) (VExt x' b' f' g' p') =
  and [x == x', conv1 k b b', conv1 k f f', conv1 k g g', conv1 k p p']
conv k (VFst u) (VFst u')                     = conv1 k u u'
conv k (VSnd u) (VSnd u')                     = conv1 k u u'
conv k (VInh u) (VInh u')                     = conv1 k u u'
conv k (VInc u) (VInc u')                     = conv1 k u u'
conv k (VSquash x u v) (VSquash x' u' v')     =
  and [x == x', conv1 k u u', conv1 k v v']
conv k (VCon c us) (VCon c' us') =
  (c == c') && and [conv1 k u u' | u <- us | u' <- us']
conv k (Kan Fill v box) (Kan Fill v' box')    =
  and $ [conv1 k v v', convBox k box box']
conv k (Kan Com v box) (Kan Com v' box')      =
  and $ [conv1 k v v', convBox k (swap box x y) (swap box' x' y)]
  where y      = fresh ((v,v'),(box,box'))
        (x,x') = (pname box, pname box')
conv k (VComN v box) (VComN v' box')      =
  and $ [conv1 k v v', convBox k (swap box x y) (swap box' x' y)]
  where y      = fresh ((v,v'),(box,box'))
        (x,x') = (pname box, pname box')
conv k (VFillN v box) (VFillN v' box')      =
  and $ [conv1 k v v', convBox k (swap box x y) (swap box' x' y)]
  where y      = fresh ((v,v'),(box,box'))
        (x,x') = (pname box, pname box')
conv k (VEquivEq x a b f s t) (VEquivEq x' a' b' f' s' t') =
  and [x == x', conv1 k a a', conv1 k b b',
       conv1 k f f', conv1 k s s', conv1 k t t']
conv k (VEquivSquare x y a s t) (VEquivSquare x' y' a' s' t') =
  and [x == x', y == y', conv1 k a a', conv1 k s s', conv1 k t t']
conv k (VPair x u v) (VPair x' u' v')     =
  and [x == x', conv1 k u u', conv1 k v v']
conv k (VSquare x y u) (VSquare x' y' u') =
  and [x == x', y == y', conv1 k u u']
conv k (VComp box) (VComp box')           =
  convBox k (swap box x y) (swap box' x' y)
  where y      = fresh (box,box')
        (x,x') = (pname box, pname box')
conv k (VFill x box) (VFill x' box')      =
  convBox k (swap box x y) (swap box' x' y)
  where y      = fresh (box,box')
conv k (VSPair u v)   (VSPair u' v')   = conv1 k u u' && conv1 k v v'
conv k (VSPair u v)   w                = conv1 k u (fstSVal w) && conv1 k v (sndSVal w)
conv k w              (VSPair u v)     = conv1 k (fstSVal w) u && conv1 k (sndSVal w) v
conv k (VApp u v)     (VApp u' v')     = conv1 k u u' && conv1 k v v'
conv k (VAppName u x) (VAppName u' x') = conv1 k u u' && (x == x')
conv k (VSplit u v)   (VSplit u' v')   = conv1 k u u' && conv1 k v v'
conv k (VVar x d)     (VVar x' d')     = (x == x')   && (d == d')
conv k (VInhRec b p phi v) (VInhRec b' p' phi' v') =
  and [conv1 k b b', conv1 k p p', conv1 k phi phi', conv1 k v v']
conv k VCircle        VCircle          = True
conv k VBase          VBase            = True
conv k (VLoop x)      (VLoop y)        = x == y
conv k (VCircleRec f b l v) (VCircleRec f' b' l' v') =
  and [conv1 k f f', conv1 k b b', conv1 k l l', conv1 k v v']
conv k VI             VI               = True
conv k VI0            VI0              = True
conv k VI1            VI1              = True
conv k (VLine x)      (VLine y)        = x == y
conv k (VIntRec f s e l u) (VIntRec f' s' e' l' u') =
  and [conv1 k f f', conv1 k s s', conv1 k e e', conv1 k l l', conv1 k u u']
conv k _              _                = False

convEnv :: Int -> Env -> Env -> Bool
convEnv k e e' = and [conv1 k v v' | v <- valOfEnv e | v' <- valOfEnv e']
