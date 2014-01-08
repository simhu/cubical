{-# LANGUAGE ParallelListComp #-}
module Eval where

import Control.Arrow (second)
import Control.Monad
import Control.Applicative
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

unCompAs :: Val -> Name -> Maybe (Box Val)
unCompAs (VComp box) y = return $ swap box (pname box) y
unCompAs v           _ = fail   $ "unCompAs: " ++ show v ++ " is not a VComp"

unFillAs :: Val -> Name -> Maybe (Box Val)
unFillAs (VFill x box) y = return $ swap box x y
unFillAs v             _ = fail   $ "unFillAs: " ++ show v ++ " is not a VFill"

appName :: Val -> Name -> Val
appName (Path x u) y = swap u x y -- valid only when y is not a free name of u
                                  -- (see Pitts' concretisation)
appName v y          = VAppName v y

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
      lookBox (x,dir) (mapBox (`face` (z,down)) b)
    | x == y && dir == dir'                ->
        VComp $ mapBox (`face` (z,up)) b
  VApp u v        -> VApp (fc u) (fc v)
  VAppName u n    -> VAppName (fc u) (faceName n xdir) 
  VBranch u v     -> VBranch (fc u) (fc v)
  VVar s d        -> VVar s [faceName n xdir | n <- d]

faceName :: Name -> Side -> Name
faceName 0 _                 = 0
faceName 1 _                 = 1
faceName x (y,d) | x == y    = d
                 | otherwise = x

-- Compute the face of an environment
faceEnv :: Env -> Side -> Env
faceEnv e xd = mapEnv (`face` xd) e

faceM :: Monad m => m Val -> Side -> m Val
faceM mv s = do {v <- mv; return $ face v s}

idV :: Val
idV = Ter (Lam "x" (Var "x")) Empty

idVPair :: Name -> Val -> Val
idVPair x v = VPair x (v `face` (x,down)) v

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
        box = Box up x (eval e t) []
eval e (TransURef t) = Path (fresh e) (eval e t)
eval e (TransUEquivEq a b f s t u) = Path x pv -- TODO: Check this!
  where x   = fresh e
        pv  = fill (eval e b) box
        box = Box up x (app (eval e f) (eval e u)) []
eval e (J a u c w _ p) = com (app (app cv omega) sigma) box
  where
    x:y:_ = freshs e
    uv    = eval e u
    pv    = appName (eval e p) x
    theta = fill (eval e a) (Box up x uv [((y,down),uv),((y,up),pv)])
    sigma = Path x theta
    omega = theta `face` (x,up)
    cv    = eval e c
    box   = Box up y (eval e w) []
eval e (JEq a u c w) = Path y $ fill (app (app cv omega) sigma) box
  where
    x:y:_ = freshs e
    uv    = eval e u
    theta = fill (eval e a) (Box up x uv [((y,down),uv),((y,up),uv)])
    sigma = Path x theta
    omega = theta `face` (x,up)
    cv    = eval e c
    box   = Box up y (eval e w) []
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
  where x:y:_ = freshs e
eval e (Trans c p t) = com (app (eval e c) pv) box
  where x   = fresh e
        pv  = appName (eval e p) x
        box = Box up x (eval e t) []
eval e (MapOnPath f p) = Path x $ app (eval e f) (appName (eval e p) x)
  where x   = fresh e


inhrec :: Val -> Val -> Val -> Val -> Val
inhrec _ _ phi (VInc a)          = app phi a
inhrec b p phi (VSquash x a0 a1) = appName (app (app p b0) b1) x
  where fc w d = w `face` (x,d)
        b0     = inhrec (fc b down) (fc p down) (fc phi down) a0
        b1     = inhrec (fc b up)   (fc p up)   (fc phi up)   a1
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
  where x    = fresh (vid, box)
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
fill v@(Ter (LSum _ nass) env) box = Kan Fill v box
fill (VEquivSquare x y a s t) box@(Box dir x' vx' nvs) =
  VSquare x y v
  where v = fill a $ modBox unPack box

        unPack :: (Name,Dir) -> Val -> Val
        unPack (z,c) v | z /= x && z /= y  = unSquare v
                       | z == y && c == up = sndVal v
                       | otherwise         = v

-- a and b should be independent of x
fill veq@(VEquivEq x a b f s t) box@(Box dir z vz nvs)
  | x /= z && x `notElem` nonPrincipal box =
    let ax0  = fill a (mapBox fstVal box)
        bx0  = app f ax0
        bx   = mapBox sndVal box
        bx1  = fill b $ mapBox (`face` (x,up)) bx
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
     let y  = fresh (veq, box)
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
      add :: Side -> Maybe Val  -- TODO: Is this correct? Do we have
                          -- to consider the auxsides?
--      add yc = fill (lookBox yc tbox) (mapBox (`face` yc) box)
      add yc = fill (lookBox yc tbox) <$> boxM (mapBox (pickout yc) box)
      newBox = boxM $ addFunBox toAdd add (mapBox pure box)
--    in traceb ("Kan Com 1 " ++ "newBox = " ++ show newBox ++ "\n") $ fill v newBox
    in case newBox of
       Just box -> traceb ("Kan Com 1 ") $ fill v box
       Nothing  -> Kan Com v box
  | x' `notElem` nK =
    let principal :: Maybe Val
        principal = fill tx <$> boxM (mapBox (pickout (x,tdir')) boxL)
        nonprincipal :: [(Side,Maybe Val)]
        nonprincipal =
          [ let side = [((x,tdir) , Just $ lookBox yc box)
                       ,((x,tdir'), principal `faceM` yc)]
            in (yc, fill (lookBox yc tbox) <$> boxM
                    (side `appendSides` mapBox (pickout yc) boxL))
          | yc <- allDirs nK ]
        newBox = boxM $ Box tdir x principal nonprincipal
    in case newBox of
       Just box -> traceb ("Kan Com 2 ") VComp box
       Nothing  -> Kan Com v box
  | x' `elem` nK =
    let -- assumes zc in defBox tbox
      auxsides zc = [ (yd,pickout zc (lookBox yd box)) | yd <- allDirs nL ]
      -- extend input box along x with orientation tdir'; results
      -- in the non-principal faces on the intersection of defBox
      -- box and defBox tbox; note, that the intersection contains
      -- (x',dir'), but not (x',dir) (and (x,_))
      npintbox = modBox (\yc boxside -> fill (lookBox yc tbox) <$> boxM
                                  (Box tdir' x (pure boxside) (auxsides yc)))
                        (subBox (nK `intersect` nJ) box)
      npint = fromBox npintbox
      npintfacebox = mapBox (`faceM` (x,tdir')) npintbox
      principal = fill tx <$> boxM (auxsides (x,tdir') `appendSides` npintfacebox)
      nplp  = principal `faceM` (x',dir)
      nplnp = auxsides (x',dir)
              ++ map (\(yc,v) -> (yc,v `faceM` (x',dir))) (sides npintbox)
      -- the missing non-principal face on side (x',dir)
      nplast = ((x',dir),fill (lookBox (x',dir) tbox) <$> boxM (Box tdir x nplp nplnp))
      newBox = boxM $ Box tdir x principal (nplast:npint)
    in case newBox of
       Just box -> traceb "Kan Com 3" $ VComp box
       Nothing  -> Kan Com v box
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
        pickout :: Side -> Val -> Maybe Val
        pickout zd vcomp = lookBox zd <$> unCompAs vcomp z

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
      principal = fill (lookBox (x',tdir') tbox) <$>
                  boxM (Box up z (Just boxp) (auxsides (x',tdir')))
      nonprincipal =
        [ (zc,
           let principzc = Just $ lookBox zc box
               sides = [((x,tdir'),principal `faceM` zc)
                       ,((x,tdir),principzc)] -- "degenerate" along z!
           in fill (lookBox zc tbox) <$>
              boxM (Box up z principzc (sides ++ auxsides zc)))
        | zc <- allDirs nK ]
      newBox = boxM $ Box tdir x' principal nonprincipal
    in case newBox of
      Just box -> traceb ("Kan Fill VU Case 2 v= ")  VFill z box
                  -- ++ show v ++ "\nbox= " ++ show box)
      Nothing  -> Kan Fill v box

  | x == x' && dir == mirror tdir = -- assumes K subset x',J
      let      -- the principal side of box must be a VComp
          upperbox = unCompAs (lookBox (x,dir') box) x
          nonprincipal =
            [ (zc,
               let top    = lookBox zc <$> upperbox
                   bottom = Just $ lookBox zc box
                   princ  = top `faceM` (x',tdir) -- same as: bottom `face` (x',tdir)
                   sides  = [((z,down),bottom),((z,up),top)]
               in fill (lookBox zc tbox) <$>
                    boxM (Box tdir' x princ -- "degenerate" along z!
                     (sides ++ auxsides zc)))
            | zc <- allDirs nK ]
          nonprincipalfaces =
            map (\(zc,u) -> (zc,u `faceM` (x,dir))) nonprincipal
          principal =
            fill (lookBox (x,tdir') tbox) <$>
              boxM (Box up z (lookBox (x,tdir') <$> upperbox)
                             (nonprincipalfaces ++ auxsides (x,tdir')))
          newBox = boxM $ Box tdir x' principal nonprincipal
      in case newBox of
           Just box -> traceb "Kan Fill VU Case 3" VFill z box
           Nothing  -> Kan Fill v box
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
          xaux      = unCompAs (lookBox (x,tdir) box) x
                        -- TODO: Do we need a fresh name?
          boxprinc  = unFillAs (lookBox (x',dir') box) z
          princnp   = [((z,up),lookBox (x,tdir') <$> xaux)
                      ,((z,down),Just $ lookBox (x,tdir') box)]
                      ++ auxsides (x,tdir')
          principal = fill (lookBox (x,tdir') tbox) <$> -- tx
                        boxM (Box dir x' (lookBox (x,tdir') <$> boxprinc) princnp)
          nonprincipal =
            [ let yup = lookBox yc <$> xaux
                  np  = [((z,up),yup),((z,down),Just $ lookBox yc box)
                        ,((y,c), yup `faceM` (x,tdir)) -- deg along z!
                        ,((y,mirror c), principal `faceM` yc)]
                        ++ auxsides yc
              in (yc, fill (lookBox yc tbox) <$>
                        boxM (Box dir x' (lookBox yc <$> boxprinc) np))
            | yc@(y,c) <- allDirs nK]
          newBox       = boxM $ Box tdir x' principal nonprincipal
        in case newBox of
           Just box -> traceb "Kan Fill VU Case 5" VFill z box
           Nothing  -> Kan Fill v box
  | x' `elem` nK =              -- assumes x,K subset x',J
        let -- surprisingly close to the last case of the Kan-Com-VU filling
          upperbox = unCompAs (lookBox (x,dir') box) x
          npintbox =
            modBox (\zc downside ->
                     let bottom = Just $ lookBox zc box
                         top    = lookBox zc <$> upperbox
                         princ  = Just downside -- same as bottom `face` (x',tdir) and
                                           -- top `face` (x',tdir)
                         sides  = [((z,down),bottom),((z,up),top)]
                     in fill (lookBox zc tbox) <$>  -- deg along z!
                          boxM (Box tdir' x princ (sides ++ auxsides zc)))
                   (subBox (nK `intersect` nJ) box)
          npint = fromBox npintbox
          npintfacebox = mapBox (`faceM` (x,tdir)) npintbox
          principalbox = ([((z,down),Just $ lookBox (x,tdir') box)
                         ,((z,up)  ,lookBox (x,tdir') <$> upperbox)] ++
                         auxsides (x,tdir')) `appendSides` npintfacebox
          principal = fill tx <$> boxM principalbox
          nplp   = lookBox (x',dir) <$> upperbox
          nplnp  = [((x',dir), nplp `faceM` (x',dir)) -- deg along z!
                   ,((x', dir'),principal `faceM` (x',dir))]
                   ++ auxsides (x',dir)
                   ++ map (\(zc,u) -> (zc,u `faceM` (x',dir))) (sides npintbox)
          nplast = ((x',dir),fill (lookBox (x',dir) tbox) <$> boxM (Box down z nplp nplnp))
          newBox       = boxM $ Box tdir x' principal (nplast:npint)
        in case newBox of
           Just box -> traceb "Kan Fill VU Case 6" VFill z box
           Nothing  -> Kan Fill v box
    where z     = fresh (v, box)
          nK    = nonPrincipal tbox
          nJ    = nonPrincipal box
          toAdd = nK \\ (x' : nJ)
          nL    = nJ \\ nK
          boxL  = subBox nL box
          dir'  = mirror dir
          tdir' = mirror tdir
          -- asumes zc is in the sides of tbox
          pickout zc vfill = lookBox zc <$> (unFillAs vfill z)
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
app (Ter (Branch _ nvs) e) (VCon name us) = case lookup name nvs of
    Just (xs,t)  -> eval (upds e (zip xs us)) t
    Nothing -> error $ "app: Branch with insufficient "
               ++ "arguments; missing case for " ++ name
app u@(Ter (Branch _ _) _) v = VBranch u v
app r s = VApp r s -- r should be neutral

convBox :: Int -> Box Val -> Box Val -> Bool
convBox k box@(Box d pn _ ss) box'@(Box d' pn' _ ss') = 
  if   and [d == d', pn == pn', sort np == sort np']
  then and [conv k (lookBox s box) (lookBox s box') | s <- defBox box]
  else False
  where (np, np') = (nonPrincipal box, nonPrincipal box')

mkVar :: Int -> Dim -> Val
mkVar k d = VVar ("X" ++ show k) d

conv :: Int -> Val -> Val -> Bool
conv k VU VU                 = True
conv k (Ter (Lam x u) e) (Ter (Lam x' u') e') = 
    conv (k+1) (eval (Pair e (x,v)) u) (eval (Pair e' (x',v)) u')
    where v = mkVar k $ support (e, e')
conv k (Ter (Lam x u) e) u' =
    conv (k+1) (eval (Pair e (x,v)) u) (app u' v)
    where v = mkVar k $ support e
conv k u' (Ter (Lam x u) e) =
    conv (k+1) (app u' v) (eval (Pair e (x,v)) u)
    where v = mkVar k $ support e
conv k (Ter (Branch p _) e) (Ter (Branch p' _) e') 
  | p /= p'   = False
  | otherwise = and [conv k v v' | v <- valOfEnv e | v' <- valOfEnv e']
conv k (Ter (LSum p _) e) (Ter (LSum p' _) e') 
  | p /= p'   = False
  | otherwise = and [conv k v v' | v <- valOfEnv e | v' <- valOfEnv e']
conv k (VPi u v) (VPi u' v') = conv k u u' && conv (k+1) (app v w) (app v' w) 
    where w = mkVar k $ support [u,u',v,v']
conv k (VId a u v) (VId a' u' v') = and [conv k a a', conv k u u', conv k v v']
conv k (Path x u) (Path x' u')    = conv k (swap u x z) (swap u' x' z)
  where z = fresh (u,u')
conv k (VExt x b f g p) (VExt x' b' f' g' p') =
  and [x == x', conv k b b', conv k f f', conv k g g', conv k p p']
conv k (VInh u) (VInh u')                     = conv k u u'
conv k (VInc u) (VInc u')                     = conv k u u'
conv k (VSquash x u v) (VSquash x' u' v')     =
  and [x == x', conv k u u', conv k v v']
conv k (VCon c us) (VCon c' us')              =
  and $ (c == c'):[conv k u u' | u <- us | u' <- us']
conv k (Kan Fill v box) (Kan Fill v' box')    = 
  and $ [conv k v v', convBox k box box']
conv k (Kan Com v box) (Kan Com v' box')      = 
  and $ [conv k v v', convBox k (swap box x y) (swap box' x' y)]
  where y      = fresh ((v,v'),(box,box'))
        (x,x') = (pname box, pname box')
conv k (VEquivEq x a b f s t) (VEquivEq x' a' b' f' s' t') =
  and [x == x', conv k a a', conv k b b',
       conv k f f', conv k s s', conv k t t']
conv k (VEquivSquare x y a s t) (VEquivSquare x' y' a' s' t') =
  and [x == x', y == y', conv k a a', conv k s s', conv k t t']
conv k (VPair x u v) (VPair x' u' v')     =
  and [x == x', conv k u u', conv k v v']
conv k (VSquare x y u) (VSquare x' y' u') =
  and [x == x', y == y', conv k u u']
conv k (VComp box) (VComp box')           =
  convBox k (swap box x y) (swap box' x' y)
  where y      = fresh (box,box')
        (x,x') = (pname box, pname box')
conv k (VFill x box) (VFill x' box')      =
  convBox k (swap box x y) (swap box' x' y)
  where y      = fresh (box,box')
conv k (VApp u v)     (VApp u' v')     = conv k u u' && conv k v v'
conv k (VAppName u x) (VAppName u' x') = conv k u u' && (x == x')
conv k (VBranch u v)  (VBranch u' v')  = conv k u u' && conv k v v'
conv k (VVar x d)     (VVar x' d')     = (x == x')   && (d == d')
conv k _              _                = False
