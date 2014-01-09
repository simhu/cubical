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

isCon :: Val -> Bool
isCon (VCon _ _) = True
isCon _ = False

isVFill :: Val -> Bool
isVFill (VFill _ _) = True
isVFill _           = False

isVComp :: Val -> Bool
isVComp (VComp _) = True
isVComp _         = False

isVPair :: Val -> Bool
isVPair (VPair _ _ _) = True
isVPair _ = False

isVSquare :: Val -> Bool
isVSquare (VSquare _ _ _) = True
isVSquare  _           = False


unFillAs :: Val -> Name -> Box Val
unFillAs (VFill x box) y = swap box x y
unFillAs v             _ = error $ "unFillAs: " ++ show v ++ " is not a VFill"

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
  VApp u v        -> app (fc u) (fc v)
  VAppName u n    -> appName (fc u) (faceName n xdir) 
  VBranch u v     -> app (fc u) (fc v)
  VVar s d        -> VVar s [faceName n xdir | n <- d]

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

eval :: Env -> Ter -> Val
eval _ U             = VU
eval e t@(Undef _)   = Ter t e
eval e (Var i)       = look i e
eval e (Id a a0 a1)  = VId (eval e a) (eval e a0) (eval e a1)
eval e (Refl a)      = Path (fresh e) $ eval e a
eval e (TransU p t) =
--  traceb ("evalTrans U" ++ "\nbox = " ++ showBox box ++ "\npv = " ++ show pv) (com pv box)
  com pv box
  where x   = fresh e
        pv  = appName (eval e p) x
        box = Box up x (eval e t) []
eval e (TransURef t) = Path (fresh e) (eval e t)
eval e (TransUEquivEq a b f s t u) = Path x pv -- TODO: Check this!
  where x   = fresh e
        pv  = fill (eval e b) box
        box = Box up x (app (eval e f) (eval e u)) []
eval e (J a u c w _ p) = 
 com (app (app cv omega) sigma) box
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
inhrec b p phi v = VInhRec b p phi v -- v should be neutral

kan :: KanType -> Val -> Box Val -> Val
kan Fill = fill
kan Com  = com

isNeutralFill :: Val -> Box Val -> Bool
-- isNeutralFill v box | isNeutral v = True
isNeutralFill v@(Ter (Undef _) _) box = True
isNeutralFill veq@(VEquivEq x a b f s t) box@(Box dir z vz nvs)
  | x == z && dir == down && not (isCon (app s vz)) = True
isNeutralFill v@(Kan Com VU tbox') box@(Box d x _ _) =
  not (and [isVComp (lookBox yc box) | yc <- aDs])
   where
        nK    = nonPrincipal tbox'
        nJ    = nonPrincipal box
        nL    = nJ \\ nK
        aDs   = if x `elem` nK then allDirs nL else (x,mirror d):(allDirs nL)
isNeutralFill v@(Kan Fill VU tbox') box@(Box d x _ _) =
  not (and [isVFill (lookBox yc box) | yc <- aDs])
   where
        nK    = (pname tbox'):(nonPrincipal tbox')
        nJ    = nonPrincipal box
        nL    = nJ \\ nK
        aDs   = if x `elem` nK then allDirs nL else (x,mirror d):(allDirs nL)
isNeutralFill v@(VEquivEq z a b f s t) box@(Box d x _ _) =
  not (and [isVPair (lookBox yc box) | yc <- aDs])
   where
        nJ    = nonPrincipal box
        nL    = nJ \\ [z]
        aDs   = if x == z then allDirs nL else (x,mirror d):(allDirs nL)
isNeutralFill v@(VEquivSquare y z _ _ _) box@(Box d x _ _) =
  not (and [isVSquare (lookBox yc box) | yc <- aDs])
   where
        nJ    = nonPrincipal box
        nL    = nJ \\ [y,z]
        aDs   = if x `elem` [y,z] then allDirs nL else (x,mirror d):(allDirs nL)
isNeutralFill (Ter (LSum _ _) _) (Box _ _ v nvs) =
 not (and ((isCon v):[isCon u | (_,u) <- nvs]))
isNeutralFill v box = False

-- Kan filling
fill :: Val -> Box Val -> Val
fill vid@(VId a v0 v1) box@(Box dir i v nvs) = Path x $ fill a box'
  where x    = fresh (vid, box)
        box' = (x,(v0,v1)) `consBox` mapBox (`appName` x) box
-- assumes cvs are constructor vals
fill v@(Ter (LSum _ nass) env) box@(Box _ _ (VCon n _) _)  | isNeutralFill v box = Kan Fill v box
fill v@(Ter (LSum _ nass) env) box@(Box _ _ (VCon n _) _)  | otherwise = 
 VCon n ws
  where as = case lookup n nass of
               Just as -> as
               Nothing -> error $ "fill: missing constructor "
                               ++ "in labelled sum " ++ n
        boxes = transposeBox $ mapBox unCon box
        -- fill boxes for each argument position of the constructor
        ws    = fills as env boxes
fill v@(VEquivSquare x y a s t) box@(Box dir x' vx' nvs) | isNeutralFill v box = Kan Fill v box
fill (VEquivSquare x y a s t) box@(Box dir x' vx' nvs) =
  VSquare x y v
  where v = fill a $ modBox unPack box

        unPack :: (Name,Dir) -> Val -> Val
        unPack (z,c) v | z /= x && z /= y  = unSquare v
                       | z == y && c == up = sndVal v
                       | otherwise         = v

-- a and b should be independent of x
fill veq@(VEquivEq x a b f s t) box@(Box dir z vz nvs)
  | isNeutralFill veq box = Kan Fill veq box
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
--     let y  = fresh (veq, box)
      case app s vz of
       VCon "pair" [gb,sb] ->
        let y  = fresh (veq, box)
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
       _ -> Kan Fill veq box
  | otherwise = error "fill EqEquiv"


fill v@(Kan Com VU tbox') box@(Box dir x' vx' nvs')
  | isNeutralFill v box = Kan Fill v box
  | toAdd /= [] = -- W.l.o.g. assume that box contains faces for
    let           -- the non-principal sides of tbox.
      add :: Side -> Val  -- TODO: Is this correct? Do we have
                          -- to consider the auxsides?
      add yc = fill (lookBox yc tbox `face` (x,tdir)) (mapBox (`face` yc) box)
--      add yc = fill (lookBox yc tbox) (mapBox (pickout yc) box)
      newBox = [ (n,(add (n,down),add (n,up)))| n <- toAdd ] `appendBox` box
--    in traceb ("Kan Com 1 ") $ fill v newBox
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
  | isNeutralFill v box = Kan Fill v box

  | toAdd /= [] =
    let
      add :: Side -> Val
     -- TODO: fix fill in the same way as Kan Com 1 ???
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
    case lookBox (x,dir') box of
      VComp _ -> 
        let      -- the principal side of box must be a VComp
          upperbox = unCompAs (lookBox (x,dir') box) x
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
      _ -> Kan Fill v box
  | x `notElem` nJ =  -- assume x /= x' and K subset x', J
    let
      comU   = v `face` (x,tdir) -- Kan Com VU (tbox (z=up))
      xsides = [((x,tdir), fill comU (mapBox (`face` (x,tdir)) box))
               ,((x,tdir'),fill (lookBox (x,tdir') tbox)
                            (mapBox (`face` (x,tdir)) box))]
    in       traceb "Kan Fill VU Case 4"
     fill v (xsides `appendSides` box)
  | x' `notElem` nK =  -- assumes x,K subset x',J
    case lookBox (x,tdir) box of
      VComp _ ->
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
      _ -> Kan Fill v box
  | x' `elem` nK =              -- assumes x,K subset x',J
    case lookBox (x,dir') box of
      VComp _ ->
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
      _ -> Kan Fill v box
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
com u box | isNeutralFill u box = Kan Com u box
com vid@VId{} box@(Box dir i _ _)         = fill vid box `face` (i,dir)
com veq@VEquivEq{} box@(Box dir i _ _)    = fill veq box `face` (i,dir)
com u@(Kan Com VU _) box@(Box dir i _ _)  = fill u box `face` (i,dir)
com u@(Kan Fill VU _) box@(Box dir i _ _) = fill u box `face` (i,dir)
com ter@Ter{} box@(Box dir i _ _)         = fill ter box `face` (i,dir)
com v box                                 =  Kan Com v box
-- traceb ("com " ++ "\nv = " ++ show v ++ "\n box = " ++ showBox box) (Kan Com v box)

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
app (Ter (Branch _ nvs) e) (VCon name us) = case lookup name nvs of
    Just (xs,t)  -> eval (upds e (zip xs us)) t
    Nothing -> error $ "app: Branch with insufficient "
               ++ "arguments; missing case for " ++ name
app u@(Ter (Branch _ _) _) v = VBranch u v -- v should be neutral
        -- | isNeutral v = VBranch u v
        -- | otherwise   = error $ "app: (VBranch) " ++ show v ++ " is not neutral"
app r s = VApp r s -- r should be neutral
        -- | isNeutral r = VApp r s -- r should be neutral
        -- | otherwise   = error $ "app: (VApp) " ++ show r ++ " is not neutral"

convBox :: Int -> Box Val -> Box Val -> Bool
convBox k box@(Box d pn _ ss) box'@(Box d' pn' _ ss') = 
  if   and [d == d', pn == pn', sort np == sort np']
  then and [conv1 k (lookBox s box) (lookBox s box') | s <- defBox box]
  else False
  where (np, np') = (nonPrincipal box, nonPrincipal box')

mkVar :: Int -> Dim -> Val
mkVar k d = VVar ("X" ++ show k) d

conv1 :: Int -> Val -> Val -> Bool
conv1 k u v = -- traceb (show ("\n" ++ " =? "))
              -- traceb (show u ++ " =? " ++ show v ++ "\n")
              (conv k u v)

conv :: Int -> Val -> Val -> Bool
conv k VU VU                 = True
conv k (Ter (Lam x u) e) (Ter (Lam x' u') e') = 
    conv1 (k+1) (eval (Pair e (x,v)) u) (eval (Pair e' (x',v)) u')
    where v = mkVar k $ support (e, e')
conv k (Ter (Lam x u) e) u' =
    conv1 (k+1) (eval (Pair e (x,v)) u) (app u' v)
    where v = mkVar k $ support e
conv k u' (Ter (Lam x u) e) =
    conv1 (k+1) (app u' v) (eval (Pair e (x,v)) u)
    where v = mkVar k $ support e
conv k (Ter (Branch p _) e) (Ter (Branch p' _) e') 
  | p /= p'   = False
  | otherwise = and [conv1 k v v' | v <- valOfEnv e | v' <- valOfEnv e']
conv k (Ter (LSum p _) e) (Ter (LSum p' _) e') 
  | p /= p'   = False
  | otherwise = and [conv1 k v v' | v <- valOfEnv e | v' <- valOfEnv e']
conv k (Ter (Undef p) e) (Ter (Undef p') e')
  | p /= p'   = False
  | otherwise = and [conv1 k v v' | v <- valOfEnv e | v' <- valOfEnv e']
conv k (VPi u v) (VPi u' v') = conv1 k u u' && conv1 (k+1) (app v w) (app v' w) 
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
conv k (VInh u) (VInh u')                     = conv1 k u u'
conv k (VInc u) (VInc u')                     = conv1 k u u'
conv k (VSquash x u v) (VSquash x' u' v')     =
  and [x == x', conv1 k u u', conv1 k v v']
conv k (VCon c us) (VCon c' us')          
  | c /= c'    = False
  | otherwise  = and [conv1 k u u' | u <- us | u' <- us']
conv k (Kan Fill v box) (Kan Fill v' box')    = 
  and $ [conv1 k v v', convBox k box box']
conv k (Kan Com v box) (Kan Com v' box')      = 
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
conv k (VApp u v)     (VApp u' v')     = conv1 k u u' && conv1 k v v'
conv k (VAppName u x) (VAppName u' x') = conv1 k u u' && (x == x')
conv k (VBranch u v)  (VBranch u' v')  = conv1 k u u' && conv1 k v v'
conv k (VVar x d)     (VVar x' d')     = (x == x')   && (d == d')
conv k (VInhRec b p phi v) (VInhRec b' p' phi' v') =
  and [conv1 k b b', conv1 k p p', conv1 k phi phi', conv1 k v v']
conv k _              _                = False
