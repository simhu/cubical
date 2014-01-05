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
appName (Path x u) y = swap u x y
appName v _          = error $ "appName: " ++ show v ++ " should be a path"

-- Compute the face of a value
face :: Val -> Side -> Val
face u xdir@(x,dir) =
  let fc v = v `face` (x,dir) in case u of
  VU          -> VU
  Ter t e     -> eval (e `faceEnv` xdir) t
  VId a v0 v1 -> VId (fc a) (fc v0) (fc v1)
  Path y v | x == y    -> u
           | otherwise -> Path y (fc v)
  VExt y b f g p | x == y && dir == Down -> f
                 | x == y && dir == Up   -> g
                 | otherwise             -> VExt y (fc b) (fc f) (fc g) (fc p)
  VPi a f    -> VPi (fc a) (fc f)
  VInh v     -> VInh (fc v)
  VInc v     -> VInc (fc v)
  VSquash y v0 v1 | x == y && dir == Down -> v0
                  | x == y && dir == Up   -> v1
                  | otherwise             -> VSquash y (fc v0) (fc v1)
  VCon c us -> VCon c (map fc us)
  VEquivEq y a b f s t | x == y && dir == Down -> a
                       | x == y && dir == Up   -> b
                       | otherwise             ->
                         VEquivEq y (fc a) (fc b) (fc f) (fc s) (fc t)
  VPair y a v | x == y && dir == Down -> a
              | x == y && dir == Up   -> fc v
              | otherwise             -> VPair y (fc a) (fc v)
  VEquivSquare y z a s t | x == y                -> a
                         | x == z && dir == Down -> a
                         | x == z && dir == Up   -> VEquivEq y a a idV s t
                         | otherwise             ->
                          VEquivSquare y z (fc a) (fc s) (fc t)
  VSquare y z v | x == y                -> fc v
                | x == z && dir == Down -> fc v
                | x == z && dir == Up   -> idVPair y (fc v)
                | otherwise             -> VSquare y z (fc v)
  Kan Fill a b@(Box dir' y v nvs)
    | x /= y && x `notElem` nonPrincipal b -> fill (fc a) (mapBox fc b)
    | x `elem` nonPrincipal b              -> lookBox (x,dir) b
    | x == y && dir == mirror dir'         -> v
    | otherwise                            -> com a b
  Kan Com a b@(Box dir' y v nvs)
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
      lookBox (x,dir) (mapBox (`face` (z,Down)) b)
    | x == y && dir == dir'                ->
        VComp $ mapBox (`face` (z,Up)) b

idV :: Val
idV = Ter (Lam "x" (Var "x")) Empty

idVPair :: Name -> Val -> Val
idVPair x v = VPair x (v `face` (x,Down)) v

-- Compute the face of an environment
faceEnv :: Env -> Side -> Env
faceEnv e xd = mapEnv (`face` xd) e

look :: Binder -> Env -> Val
look x (Pair s (y,u)) | x == y    = u
                      | otherwise = look x s
look x r@(PDef es r1)             = look x (upds r1 (evals r es))

cubeToBox :: Val -> Box () -> Box Val
cubeToBox v = modBox (\nd _ -> v `face` nd)

eval :: Env -> Ter -> Val
eval _ U             = VU
eval e (Var i)       = look i e
eval e (Id a a0 a1)  = VId (eval e a) (eval e a0) (eval e a1)
eval e (Refl a)      = Path (fresh e) $ eval e a
eval e (TransU p t) =
  com pv box
  where x   = fresh e
        pv  = appName (eval e p) x
        box = Box Up x (eval e t) []
eval e (TransURef t) = Path (fresh e) (eval e t)
eval e (TransUEquivEq a b f s t u) = Path x pv -- TODO: Check this!
  where x   = fresh e
        pv  = fill (eval e b) box
        box = Box Up x (app (eval e f) (eval e u)) []
eval e (J a u c w _ p) = com (app (app cv omega) sigma) box
  where
    x:y:_ = gensyms $ supportEnv e
    uv    = eval e u
    pv    = appName (eval e p) x
    theta = fill (eval e a) (Box Up x uv [((y,Down),uv),((y,Up),pv)])
    sigma = Path x theta
    omega = theta `face` (x,Up)
    cv    = eval e c
    box   = Box Up y (eval e w) []
eval e (JEq a u c w) = Path y $ fill (app (app cv omega) sigma) box
  where
    x:y:_ = gensyms $ supportEnv e
    uv    = eval e u
    theta = fill (eval e a) (Box Up x uv [((y,Down),uv),((y,Up),uv)])
    sigma = Path x theta
    omega = theta `face` (x,Up)
    cv    = eval e c
    box   = Box Up y (eval e w) []
eval e (Ext b f g p) =
  Path x $ VExt x (eval e b) (eval e f) (eval e g) (eval e p)
    where x = fresh e
eval e (Pi a b)      = VPi (eval e a) (eval e b)
eval e (Lam x t)     = Ter (Lam x t) e -- stop at lambdas
eval e (App r s)     = app (eval e r) (eval e s)
eval e (Inh a)       = VInh (eval e a)
eval e (Inc t)       = VInc (eval e t)
eval e (Squash r s)  = Path x $ VSquash x (eval e r) (eval e s)
  where x = fresh e
eval e (InhRec b p phi a)  =
  inhrec (eval e b) (eval e p) (eval e phi) (eval e a)
eval e (Where t def)       = eval (PDef def e) t
eval e (Con name ts)       = VCon name (map (eval e) ts)
eval e (Branch pr alts)    = Ter (Branch pr alts) e
eval e (LSum pr ntss)      = Ter (LSum pr ntss) e
eval e (EquivEq a b f s t) =
  Path x $ VEquivEq x (eval e a) (eval e b) (eval e f) (eval e s) (eval e t)
    where x = fresh e
eval e (EquivEqRef a s t)  =
  Path y $ Path x $ VEquivSquare x y (eval e a) (eval e s) (eval e t)
  where x:y:_ = gensyms (supportEnv e)
eval e (Trans c p t) = com (app (eval e c) pv) box
  where x   = fresh e
        pv  = appName (eval e p) x
        box = Box Up x (eval e t) []

inhrec :: Val -> Val -> Val -> Val -> Val
inhrec _ _ phi (VInc a)          = app phi a
inhrec b p phi (VSquash x a0 a1) = appName (app (app p b0) b1) x
  where fc w d = w `face` (x,d)
        b0     = inhrec (fc b Down) (fc p Down) (fc phi Down) a0
        b1     = inhrec (fc b Up)   (fc p Up)   (fc phi Up)   a1
inhrec b p phi (Kan ktype (VInh a) box@(Box dir x v nvs)) =
  kan ktype b (modBox irec box)
    where irec (j,dir) v = let fc v = v `face` (j,dir)
                         in inhrec (fc b) (fc p) (fc phi) v
inhrec b p phi v = error $ "inhrec : " ++ show v

kan :: KanType -> Val -> Box Val -> Val
kan Fill = fill
kan Com  = com

-- Kan filling
fill :: Val -> Box Val -> Val
fill vid@(VId a v0 v1) box@(Box dir i v nvs) = Path x $ fill a box'
  where x    = gensym (support vid `union` support box)
        box' = (x,(v0,v1)) `consBox` mapBox (`appName` x) box
-- assumes cvs are constructor vals
fill (Ter (LSum _ nass) env) box@(Box _ _ (VCon n _) _) = VCon n ws
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
                       | z == y && c == Up = sndVal v
                       | otherwise         = v

-- a and b should be independent of x
fill veq@(VEquivEq x a b f s t) box@(Box dir z vz nvs)
  | x /= z && x `notElem` nonPrincipal box =
    let ax0  = fill a (mapBox fstVal box)
        bx0  = app f ax0
        bx   = mapBox sndVal box
        bx1  = fill b $ mapBox (`face` (x,Up)) bx
        v    = fill b $ (x,(bx0,bx1)) `consBox` bx
    in traceb ("VEquivEq case 1" ) $ VPair x ax0 v
  | x /= z && x `elem` nonPrincipal box =
    let ax0 = lookBox (x,Down) box
        bx  = modBox (\(ny,dy) vy -> if x /= ny then sndVal vy else
                                       if dy == Down then app f ax0 else vy) box
        v   = fill b bx
    in traceb "VEquivEq case 2" $ VPair x ax0 v
  | x == z && dir == Up =
    let ax0  = vz
        bx0  = app f ax0
        v    = fill b $ Box dir z bx0 [ (nnd,sndVal v) | (nnd,v) <- nvs ]
    in traceb "VEquivEq case 3" $ VPair x ax0 v
  | x == z && dir == Down =
     let y  = gensym (support veq `union` support box)
         VCon "pair" [gb,sb] = app s vz
         vy = appName sb x

         vpTSq :: Name -> Dir -> Val -> (Val,Val)
         vpTSq nz dz (VPair z a0 v0) =
             let vp = VCon "pair" [a0, Path z v0]
                 t0 = t `face` (nz,dz)
                 b0 = vz `face` (nz,dz)
                 VCon "pair" [l0,sq0] = appName (app (app t0 b0) vp) y
             in (l0,appName sq0 x)  -- TODO: check the correctness of the square s0

         -- TODO: Use modBox!
         vsqs   = [ ((n,d),vpTSq n d v) | ((n,d),v) <- nvs]
         box1   = Box Up y gb [ (nnd,v) | (nnd,(v,_)) <- vsqs ]
         afill  = fill a box1

         acom   = afill `face` (y,Up)
         fafill = app f afill
         box2   = Box Up y vy (((x,Down),fafill) : ((x,Up),vz) :
                                      [ (nnd,v) | (nnd,(_,v)) <- vsqs ])
         bcom   = com b box2
     in traceb "VEquivEq case 4" $ VPair x acom bcom
  | otherwise = error "fill EqEquiv"

fill v@(Kan Com VU tbox') box@(Box dir x' vx' nvs')
  | toAdd /= [] = -- W.l.o.g. assume that box contains faces for
    let           -- the non-principal sides of tbox.
      add :: Side -> Val  -- TODO: Is this correct? Do we have
                          -- to consider the auxsides?
--      add yc = fill (lookBox yc tbox) (mapBox (`face` yc) box)
      add yc = fill (lookBox yc tbox) (mapBox (pickout yc) box)
      newBox = [ (n,(add (n,Down),add (n,Up)))| n <- toAdd ] `appendBox` box
--    in traceb ("Kan Com 1 " ++ "newBox = " ++ show newBox ++ "\n") $ fill v newBox
    in traceb ("Kan Com 1 ") $ fill v newBox
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
    in traceb "Kan Com 3" $ VComp newBox
  where nK    = nonPrincipal tbox
        nJ    = nonPrincipal box
        z     = gensym $ support tbox' ++ support box
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
      principal = fill (lookBox (x',tdir') tbox) (Box Up z boxp (auxsides (x',tdir')))
      nonprincipal =
        [ (zc,
           let principzc = lookBox zc box
               sides = [((x,tdir'),principal `face` zc)
                       ,((x,tdir),principzc)] -- "degenerate" along z!
           in fill (lookBox zc tbox) (Box Up z principzc (sides ++ auxsides zc)))
        | zc <- allDirs nK ]
    in     traceb ("Kan Fill VU Case 2 v= ") --  ++ show v ++ "\nbox= " ++ show box)
     VFill z (Box tdir x' principal nonprincipal)

  | x == x' && dir == mirror tdir = -- assumes K subset x',J
    let      -- the principal side of box must be a VComp
      upperbox = unCompAs (lookBox (x,dir') box) x
      nonprincipal =
        [ (zc,
           let top    = lookBox zc upperbox
               bottom = lookBox zc box
               princ  = top `face` (x',tdir) -- same as: bottom `face` (x',tdir)
               sides  = [((z,Down),bottom),((z,Up),top)]
           in fill (lookBox zc tbox)
                (Box tdir' x princ -- "degenerate" along z!
                 (sides ++ auxsides zc)))
        | zc <- allDirs nK ]
      nonprincipalfaces =
        map (\(zc,u) -> (zc,u `face` (x,dir))) nonprincipal
      principal =
        fill (lookBox (x,tdir') tbox) (Box Up z (lookBox (x,tdir') upperbox)
                                       (nonprincipalfaces ++ auxsides (x,tdir')))
    in    traceb "Kan Fill VU Case 3"
     VFill z (Box tdir x' principal nonprincipal)
  | x `notElem` nJ =  -- assume x /= x' and K subset x', J
    let
      comU   = v `face` (x,tdir) -- Kan Com VU (tbox (z=Up))
      xsides = [((x,tdir), fill comU (mapBox (`face` (x,tdir)) box))
               ,((x,tdir'),fill (lookBox (x,tdir') tbox)
                            (mapBox (`face` (x,tdir)) box))]
    in       traceb "Kan Fill VU Case 4"
     fill v (xsides `appendSides` box)
  | x' `notElem` nK =  -- assumes x,K subset x',J
      let
        xaux      = unCompAs (lookBox (x,tdir) box) x -- TODO: Do we need a fresh name?
        boxprinc  = unFillAs (lookBox (x',dir') box) z
        princnp   = [((z,Up),lookBox (x,tdir') xaux)
                    ,((z,Down),lookBox (x,tdir') box)]
                    ++ auxsides (x,tdir')
        principal = fill (lookBox (x,tdir') tbox) -- tx
                      (Box dir x' (lookBox (x,tdir') boxprinc) princnp)
        nonprincipal =
          [ let up = lookBox yc xaux
                np = [((z,Up),up),((z,Down),lookBox yc box)
                     ,((y,c), up `face` (x,tdir)) -- deg along z!
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
                       sides  = [((z,Down),bottom),((z,Up),top)]
                   in fill (lookBox zc tbox) (Box tdir' x princ -- deg along z!
                                              (sides ++ auxsides zc)))
                 (subBox (nK `intersect` nJ) box)
        npint = fromBox npintbox
        npintfacebox = mapBox (`face` (x,tdir)) npintbox
        principalbox = ([((z,Down),lookBox (x,tdir') box)
                       ,((z,Up)  ,lookBox (x,tdir')upperbox)] ++
                       auxsides (x,tdir')) `appendSides` npintfacebox
        principal = fill tx principalbox
        nplp   = lookBox (x',dir) upperbox
        nplnp  = [((x',dir), nplp `face` (x',dir)) -- deg along z!
                 ,((x', dir'),principal `face` (x',dir))]
                 ++ auxsides (x',dir)
                 ++ map (\(zc,u) -> (zc,u `face` (x',dir))) (sides npintbox)
        nplast = ((x',dir),fill (lookBox (x',dir) tbox) (Box Down z nplp nplnp))
      in       traceb "Kan Fill VU Case 6"
       VFill z (Box tdir x' principal (nplast:npint))

  where z     = gensym $ support v ++ support box
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
com vid@VId{} box@(Box dir i _ _)         = fill vid box `face` (i,dir)
com ter@Ter{} box@(Box dir i _ _)         = fill ter box `face` (i,dir)
com veq@VEquivEq{} box@(Box dir i _ _)    = fill veq box `face` (i,dir)
com u@(Kan Com VU _) box@(Box dir i _ _)  = fill u box `face` (i,dir)
com u@(Kan Fill VU _) box@(Box dir i _ _) = fill u box `face` (i,dir)
com v box                                 = Kan Com v box

appBox :: Box Val -> Box Val -> Box Val
appBox (Box dir x v nvs) (Box _ _ u nus) = Box dir x (app v u) nvus
  where nvus      = [ (nnd,app v (lookup' nnd nus)) | (nnd,v) <- nvs ]
        lookup' x = fromMaybe (error "appBox") . lookup x

app :: Val -> Val -> Val
app (Ter (Lam x t) e) u                         = eval (Pair e (x,u)) t
app (Kan Com (VPi a b) box@(Box dir x v nvs)) u =
  traceb ("Pi Com\n ")
  com (app b ufill) (appBox box bcu)
  where ufill = fill a (Box (mirror dir) x u [])
        bcu   = cubeToBox ufill (shapeOfBox box)
app kf@(Kan Fill (VPi a b) box@(Box dir i w nws)) v =
  traceb ("Pi fill ") $ answer
  where x     = gensym (support kf `union` support v)
        u     = v `face` (i,dir)
        ufill = fill a (Box (mirror dir) i u [])
        bcu   = cubeToBox ufill (shapeOfBox box)
        vfill = fill a (Box (mirror dir) i u [((x,Down),ufill),((x,Up),v)])
        vx    = fill (app b ufill) (appBox box bcu)
        vi0   = app w (vfill `face` (i,Down))
        vi1   = com (app b ufill) (appBox box bcu)
        nvs   = [ ((n,d),app ws (vfill `face` (n,d))) | ((n,d),ws) <- nws ]
        answer = com (app b vfill) (Box Up x vx (((i,Down),vi0) : ((i,Up),vi1):nvs))
app vext@(VExt x bv fv gv pv) w = com (app bv w) (Box Up y pvxw [((x,Down),left),((x,Up),right)])
  -- NB: there are various choices how to construct this
  where y     = gensym (support vext `union` support w)
        w0    = w `face` (x,Down)
        left  = app fv w0
        right = app gv (swap w x y)
        pvxw  = appName (app pv w0) x
app (Ter (Branch _ nvs) e) (VCon name us) = case lookup name nvs of
    Just (xs,t)  -> eval (upds e (zip xs us)) t
    Nothing -> error $ "app: Branch with insufficient "
               ++ "arguments; missing case for " ++ name
app r s = error $ "app"  ++ show r ++ show s
