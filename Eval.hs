module Eval where

-- import Control.Arrow hiding (app)
import Data.Either
import Data.List
import Data.Maybe

import Debug.Trace

import Core

type Name = Integer
type Dim  = [Name]
data Dir  = Up | Down deriving (Eq, Show)

mirror :: Dir -> Dir
mirror Up = Down
mirror Down = Up

gensym :: Dim -> Name
gensym [] = 0
gensym xs = maximum xs + 1

gensyms :: Dim -> [Name]
gensyms d = let x = gensym d in x : gensyms (x : d)

-- The pair of values is (down,up).
data Box a = Box Dir Name a [((Name,Dir),a)]
  deriving (Eq,Show)

mapBox :: (a -> b) -> Box a -> Box b
mapBox f (Box d n x xs) = Box d n (f x) [ (nnd,f v) | (nnd,v) <- xs ]
                          -- (map (second f) xs)

instance Functor Box where fmap = mapBox

lookBox :: Show a => (Name,Dir) -> Box a -> a
lookBox (y,dir) (Box d x v _) | x == y && mirror d == dir = v
lookBox xd box@(Box _ _ _ nvs)    | otherwise = case lookup xd nvs of
  Just v  -> v
  Nothing -> error $ "lookBox: box not defined on " ++ show xd ++ "\nbox = " ++ show box

nonPrincipal :: Box a -> [Name]
nonPrincipal (Box _ _ _ nvs) = nub $ map (fst . fst) nvs

defBox :: Box a -> [(Name, Dir)]
defBox (Box d x _ nvs) = (x,mirror d) : [ zd | (zd,_) <- nvs ]

fromBox :: Box a -> [((Name,Dir),a)]
fromBox (Box d x v nvs) = ((x,d),v) : nvs

-- toBox :: Dir -> Name -> [((Name,Dir),a)] -> Box a
-- toBox d x (nv@(zd,v):nvs) | zd == (x, mirror d) = Box d x v nvs
--                           | otherwise = let Box d' x' nv' nvs' = toBox d x nvs
--                                         in  Box d' x' nv' (nv:nvs')
-- toBox _ _ [] = error $ "toBox: not a box!"

modBox :: ((Name,Dir) -> a -> b) -> Box a -> Box b
modBox f (Box dir x v nvs) =
  Box dir x (f (x,mirror dir) v) [ (nd,f nd v) | (nd,v) <- nvs ]

-- Restricts the non-principal faces to np.
subBox :: [Name] -> Box a -> Box a
subBox np (Box dir x v nvs) = Box dir x v [ nv | nv@((n,_),_) <- nvs, n `elem` np]

cubeToBox :: Val -> Box () -> Box Val
cubeToBox v box = modBox (\nd _ -> v `face` nd) box
--  Box dir x (face v x (mirror dir)) [ ((n,d),face v n d) | ((n,d),_) <- nvs ]

shapeOfBox :: Box a -> Box ()
shapeOfBox = mapBox (const ())

-- fst is down, snd is up
consBox :: (Name,(a,a)) -> Box a -> Box a
consBox (n,(v0,v1)) (Box dir x v nvs) =
  Box dir x v $ ((n,Down),v0) : ((n,Up),v1) : nvs

appendBox :: [(Name,(a,a))] -> Box a -> Box a
appendBox xs b = foldr consBox b xs

appendSides :: [((Name,Dir), a)] -> Box a -> Box a
appendSides sides (Box dir x v nvs) = Box dir x v (sides ++ nvs)

-- TODO: This is not really the right way to do it.
arrangeSide :: Show a => Name -> (Dir, a) -> (Dir, a) -> (Name, (a,a))
arrangeSide n (Down, u) (Up, u') = (n, (u,u'))
arrangeSide n (Up, u) (Down, u') = (n, (u',u))
arrangeSide _ a b = error $ "arrangeSide: not a valid side: " ++ show a
                    ++ " and " ++ show b


data KanType = Fill | Com deriving (Show, Eq)

data Val = VU
         | Ter Ter Env
         | VId Val Val Val
         | Path Name Val             -- tag values which are paths
         | VExt Name Val Val Val Val -- has dimension (name:dim);
                                     -- vals of dimension dim
         | VPi Val Val
         | VInh Val
         | VInc Val
         | VSquash Name Val Val  -- connects the two values along the name
         | VCon Ident [Val]
         | Kan KanType Val (Box Val)
         | VEquivEq Name Val Val Val Val Val -- of type U connecting a and b along x
         | VEquivSquare Name Name Val Val Val -- names x, y and values a, s, t
           -- VEquivEq x a b f s t
         | VPair Name Val Val -- of type VEquivEq
         | VSquare Name Name Val
         | VComp (Box Val)    -- a value of type Kan Com VU (Box (type of values))
         | VFill Name (Box Val) -- a value of type Kan Fill VU (Box
                                -- (type of values minus name)); the name is bound
  deriving (Show, Eq)

fstVal, sndVal :: Val -> Val
fstVal (VPair _ a _) = a
fstVal x             = error $ "error fstVal: " ++ show x
sndVal (VPair _ _ v) = v
sndVal x             = error $ "error sndVal: " ++ show x

data Env = Empty
         | Pair Env Val
         | PDef [Ter] Env
  deriving (Eq,Show)

upds :: Env -> [Val] -> Env
upds = foldl Pair

look :: Int -> Env -> Val
look 0 (Pair _ u)     = u
look k (Pair s _)     = look (k-1) s
look k r@(PDef es r1) = look k (upds r1 (evals r es))

ter :: Ter -> Env -> Val
ter t e = eval e t

evals :: Env -> [Ter] -> [Val]
evals e = map (eval e)

mapEnv :: (Val -> Val) -> Env -> Env
mapEnv _ Empty = Empty
mapEnv f (Pair e v) = Pair (mapEnv f e) (f v)
mapEnv f (PDef ts e) = PDef ts (mapEnv f e)

faceEnv :: Env -> (Name,Dir) -> Env
faceEnv e xd = mapEnv (\u -> u `face` xd) e

face :: Val -> (Name,Dir) -> Val
face u xdir@(x,dir) =
  let fc v = v `face` (x,dir) in case u of
  VU          -> VU
  Ter t e     -> ter t (e `faceEnv` xdir)
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
idV = Ter (Lam (Var 0)) Empty

idVPair :: Name -> Val -> Val
idVPair x v = VPair x (v `face` (x,Down)) v

unions :: Eq a => [[a]] -> [a]
unions = foldr union []

unionsMap :: Eq b => (a -> [b]) -> [a] -> [b]
unionsMap f = unions . map f

-- test that names only occur once in support
support :: Val -> [Name]
support VU                = []
support (Ter _ e)         = supportEnv e
support (VId a v0 v1)     = unionsMap support [a,v0,v1]
support (Path x v)        = delete x $ support v
support (VInh v)          = support v
support (VInc v)          = support v
support (VPi v1 v2)       = unionsMap support [v1,v2]
support (VCon _ vs)       = unionsMap support vs
support (VSquash x v0 v1) = [x] `union` unionsMap support [v0,v1]
support (VExt x b f g p)  = [x] `union` unionsMap support [b,f,g,p]
support (Kan Fill a box)  = support a `union` supportBox box
support (Kan Com a box@(Box _ n _ _)) =
  delete n (support a `union` supportBox box)
support (VEquivEq x a b f s t)    = [x] `union` unionsMap support [a,b,f,s,t]
support (VPair x a v)             = [x] `union` unionsMap support [a,v]
support (VComp box@(Box _ n _ _)) = delete n $ supportBox box
support (VFill x box)             = delete x $ supportBox box

supportBox :: Box Val -> [Name]
supportBox (Box dir n v vns) = [n] `union` support v `union`
  unions [ [y] `union` support v | ((y,dir'),v) <- vns ]

supportEnv :: Env -> [Name]
supportEnv Empty      = []
supportEnv (Pair e v) = supportEnv e `union` support v
supportEnv (PDef _ e) = supportEnv e

-- TODO: Typeclass for freshness!
fresh :: Val -> Name
fresh = gensym . support

freshEnv :: Env -> Name
freshEnv = gensym . supportEnv

swapName :: Name -> Name -> Name -> Name
swapName z x y | z == x    = y
               | z == y    = x
               | otherwise = z

swapEnv :: Env -> Name -> Name -> Env
swapEnv e x y = mapEnv (\u -> swap u x y) e

swapBox :: Box Val -> Name -> Name -> Box Val
swapBox (Box dir z v nvs) x y =
  let sw u = swap u x y
  in Box dir (swapName z x y) (sw v)
         [ ((swapName n x y,nd),sw v) | ((n,nd),v) <- nvs ]

swap :: Val -> Name -> Name -> Val
swap u x y =
  let sw u = swap u x y in case u of
  VU          -> VU
  Ter t e     -> Ter t (swapEnv e x y)
  VId a v0 v1 -> VId (sw a) (sw v0) (sw v1)
  Path z v | z /= x && z /= y    -> Path z (sw v)
           | otherwise -> let z' = gensym ([x] `union` [y] `union` support v)
                              v' = swap v z z'
                          in Path z' (sw v')
  VExt z b f g p  -> VExt (swapName z x y) (sw b) (sw f) (sw g) (sw p)
  VPi a f         -> VPi (sw a) (sw f)
  VInh v          -> VInh (sw v)
  VInc v          -> VInc (sw v)
  VSquash z v0 v1 -> VSquash (swapName z x y) (sw v0) (sw v1)
  VCon c us       -> VCon c (map sw us)
  VEquivEq z a b f s t ->
    VEquivEq (swapName z x y) (sw a) (sw b) (sw f) (sw s) (sw t)
  VPair z a v  -> VPair (swapName z x y) (sw a) (sw v)
  VEquivSquare z w a s t ->
    VEquivSquare (swapName z x y) (swapName w x y) (sw a) (sw s) (sw t)
  VSquare z w v -> VSquare (swapName z x y) (swapName w x y) (sw v)
  Kan Fill a b  -> fill (sw a) (swapBox b x y)
  Kan Com a b@(Box _ z _ _)
    | z /= x && z /= y -> com (sw a) (swapBox b x y)
    | otherwise -> let z' = gensym ([x] `union` [y] `union` support u)
                       a' = swap a z z'
                   in sw (Kan Com a' (swapBox b z z'))
  VComp b@(Box _ z _ _)
    | z /= x && z /= y -> VComp (swapBox b x y)
    | otherwise -> let z' = gensym ([x] `union` [y] `union` support u)
                   in sw (VComp (swapBox b z z'))
  VFill z b@(Box dir n _ _)
    | z /= x && z /= x -> VFill z (swapBox b x y)
    | otherwise        -> let
      z' = gensym ([x] `union` [y] `union` supportBox b)
      in sw (VFill z' (swapBox b z z'))


appName :: Val -> Name -> Val
appName (Path x u) y = swap u x y
appName v _          = error $ "appName: should be a path: " ++ show v

eval :: Env -> Ter -> Val
eval _ U             = VU
eval e (Var i)       = look i e
eval e (Id a a0 a1)  = VId (eval e a) (eval e a0) (eval e a1)
eval e (Refl a)      = Path (freshEnv e) $ eval e a
eval e (Trans c p t) = com (app (eval e c) pv) box
  where x   = freshEnv e
        pv  = appName (eval e p) x
        box = Box Up x (eval e t) []
eval e (TransInv c p t) = com (app (eval e c) pv) box
  where x   = freshEnv e
        pv  = appName (eval e p) x
        box = Box Down x (eval e t) []
eval e (TransU p t) = -- trace ("TransU pv= " ++ show pv)
  com pv box
  where x   = freshEnv e
        pv  = appName (eval e p) x
        box = Box Up x (eval e t) []
eval e (TransURef t) = Path (freshEnv e) (eval e t)
eval e (TransUEquivEq a b f s t u) = Path x pv -- TODO: Check this!
  where x   = freshEnv e
        pv  = fill (eval e b) box
        box = Box Up x (app (eval e f) (eval e u)) []
-- TODO: Throw out _, not needed?
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
    where x = freshEnv e
eval e (Pi a b)      = VPi (eval e a) (eval e b)
eval e (Lam t)       = Ter (Lam t) e -- stop at lambdas
eval e (App r s)     = app (eval e r) (eval e s)
eval e (Inh a)       = VInh (eval e a)
eval e (Inc t)       = VInc (eval e t)
eval e (Squash r s)  = Path x $ VSquash x (eval e r) (eval e s)
  where x = freshEnv e
eval e (InhRec b p phi a)  =
  inhrec (eval e b) (eval e p) (eval e phi) (eval e a)
eval e (Where t def)       = eval (PDef def e) t
eval e (Con name ts)       = VCon name (map (eval e) ts)
eval e (Branch alts)       = Ter (Branch alts) e
eval e (LSum ntss)         = Ter (LSum ntss) e
eval e (EquivEq a b f s t) =
  Path x $ VEquivEq x (eval e a) (eval e b) (eval e f) (eval e s) (eval e t)
    where x = freshEnv e
eval e (EquivEqRef a s t)  =
  Path y $ Path x $ VEquivSquare x y (eval e a) (eval e s) (eval e t)
  where x:y:_ = gensyms (supportEnv e)

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

kan :: KanType -> Val -> Box Val -> Val
kan Fill = fill
kan Com  = com

unCon :: Val -> [Val]
unCon (VCon _ vs) = vs
unCon v           = error $ "unCon: not a constructor: " ++ show v

unCompAs :: Val -> Name -> Box Val
unCompAs (VComp box@(Box _ x _ _)) y = swapBox box x y
unCompAs v _ = error $ "unCompAs: not a VComp: " ++ show v

unFillAs :: Val -> Name -> Box Val
unFillAs (VFill x box) y = swapBox box x y
unFillAs v             _ = error $ "unFillAs: not a VFill: " ++ show v

unSquare :: Val -> Val
unSquare (VSquare _ _ v) = v
unSquare v               = error $ "unSquare bad input: " ++ show v

sndPair :: Val -> Val
sndPair (VPair _ _ v) = v
sndPair v             = error $ "sndPair bad input: " ++ show v

-- TODO: Clean.
transposeBox :: Box [Val] -> [Box Val]
transposeBox b@(Box dir _ [] _)      = []
transposeBox (Box dir x (v:vs) nvss) =
  Box dir x v [ (nnd,head vs) | (nnd,vs) <- nvss ] :
  transposeBox (Box dir x vs [ (nnd,tail vs) | (nnd,vs) <- nvss ])

-- Kan filling
fill :: Val -> Box Val -> Val
fill vid@(VId a v0 v1) box@(Box dir i v nvs) = Path x $ fill a box'
  where x    = gensym (support vid `union` supportBox box)
        box' = (x,(v0,v1)) `consBox` mapBox (`appName` x) box
-- assumes cvs are constructor vals
fill (Ter (LSum nass) e) box@(Box _ _ (VCon n _) _) = VCon n ws
  where as = case lookup n nass of
               Just as -> as
               Nothing -> error $ "fill: missing constructor "
                               ++ "in labelled sum " ++ n
        boxes :: [Box Val]
        boxes = transposeBox $ mapBox unCon box
        -- fill boxes for each argument position of the constructor
        ws    = fills as e boxes
fill (VEquivSquare x y a s t) box@(Box dir x' vx' nvs) =
  VSquare x y v
  where v = fill a $ modBox unPack box

        unPack :: (Name,Dir) -> Val -> Val
        unPack (z,c) v | z /= x && z /= y  = unSquare v
                       | z == y && c == Up = sndPair v
                       | otherwise         = v

-- a and b should be independent of x
fill veq@(VEquivEq x a b f s t) box@(Box dir z vz nvs)
  | x /= z && x `notElem` nonPrincipal box =
    let ax0  = fill a (mapBox fstVal box)
        bx0  = app f ax0
        bx   = mapBox sndVal box
        bx1  = fill b $ mapBox (`face` (x,Up)) bx
        v    = fill b $ (x,(bx0,bx1)) `consBox` bx
    in trace "VEquivEq case 1" $ VPair x ax0 v
  | x /= z && x `elem` nonPrincipal box =
    let ax0 = lookBox (x,Down) box
        bx  = modBox (\(ny,dy) vy -> if x /= ny then sndVal vy else
                                       if dy == Down then app f ax0 else vy) box
        v   = fill b bx
    in trace "VEquivEq case 2" VPair x ax0 v
  | x == z && dir == Up =
    let ax0  = vz
        bx0  = app f ax0
        v    = fill b $ Box dir z bx0 [ (nnd,sndVal v) | (nnd,v) <- nvs ]
    in trace ("VEquivEq case 3") -- \nax0 = " ++ show ax0 ++ "\nbx0 = " ++ show bx0)
       VPair x ax0 v
  | x == z && dir == Down =
     let y  = gensym (support veq `union` supportBox box)
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
     in trace ("VEquivEq case 4") -- \n" ++ "box1 = " ++ show box1 ++ "\nbox2 = " ++ show box2)
        VPair x acom bcom
  | otherwise = error "fill EqEquiv"

fill v@(Kan Com VU tbox@(Box tdir x tx nvs)) box@(Box dir x' vx' nvs')
  | toAdd /= [] = -- W.l.o.g. assume that box contains faces for
    let               -- the non-principal sides of tbox.
      add :: (Name,Dir) -> Val  -- TODO: Is this correct? Do we have
                                -- to consider the auxsides?
      add zc@(z,c) = fill (lookBox zc tbox) (mapBox (`face` (z,c)) box)
      newBox = [ (n,(add (n,Down),add (n,Up)))| n <- toAdd ] `appendBox` box
    in trace ("Kan Com 1") -- \nnewBox " ++ show newBox)
       fill v newBox
  | x' `notElem` nK =
    let principal = fill tx (mapBox (pickout (x,dir')) boxL)
        nonprincipal =
          [ let side = arrangeSide x (tdir,lookBox zd box)
                       (tdir',principal `face` (z,d))
            in (zd, fill (lookBox zd tbox)
                    (side `consBox` mapBox (pickout zd) boxL))
          | zd@(z,d) <- allDirs nK ]
        newBox = Box tdir x principal nonprincipal
    in trace ("Kan Com 2\nnewBox " ++ show newBox) VComp newBox
  | x' `elem` nK =
    let -- assumes zc in defBox tbox
      -- TODO: same as mapBox (pickout zd) boxL? Merge with above?
      auxsides zc = trace "let1" [ (yd,pickout zc (lookBox yd box)) | yd <- allDirs nL ]
      -- extend input box along x' with orientation tdir'; results
      -- in the non-principal faces on the intersection of defBox
      -- box and defBox tbox; note, that the intersection contains
      -- (x',dir'), but not (x',dir) (and (x,_))
      npintbox@(Box _ _ _ npintaux) = trace "let2"
        modBox (\ zc boxside -> fill (lookBox zc tbox)
                                  (Box tdir' x boxside (auxsides zc)))
          (subBox nK box)
      npint = trace "let3" fromBox npintbox
      npintfacebox = trace "let4" mapBox (`face` (x,tdir')) npintbox
      principal = trace "let5" fill tx (auxsides (x,tdir') `appendSides` npintfacebox)
      nplp  = trace "let6" principal `face` (x',dir)
      nplnp = trace "let7" auxsides (x',dir)
              ++ map (\(zc,v) -> (zc,v `face` (x',dir))) npintaux
      -- the missing non-principal face on side (x',dir)
      nplast = trace "let8" ((x',dir),fill (lookBox (x',dir) tbox) (Box tdir x nplp nplnp))
      newBox = trace "let9" Box tdir x principal (nplast:npint)
    in trace ("Kan Com 3") -- \nnewBox " ++ show newBox)
       VComp newBox
  where nK    = nonPrincipal tbox
        nJ    = nonPrincipal box
        z     = gensym $ support v ++ supportBox box
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
    let                         -- TODO: Okay?
      add :: (Name,Dir) -> Val
      add zc = fill (lookBox zc tbox) (mapBox (`face` zc) box)
      newBox = [ (zc,add zc) | zc <- allDirs toAdd ] `appendSides` box
    in trace "Kan Fill VU Case 1" fill v newBox            -- W.l.o.g. nK subset x:nJ
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
    in     trace ("Kan Fill VU Case 2 v= " ++ show v ++ "\nbox= " ++ show box)
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
    in    trace "Kan Fill VU Case 3"
     VFill z (Box tdir x' principal nonprincipal)
  | x `notElem` nJ =  -- assume x /= x' and K subset x', J
    let
      comU   = v `face` (x,tdir) -- Kan Com VU (tbox (z=Up))
      xsides = [((x,tdir), fill comU (mapBox (`face` (x,tdir)) box))
               ,((x,tdir'),fill (lookBox (x,tdir') tbox)
                            (mapBox (`face` (x,tdir)) box))]
    in       trace "Kan Fill VU Case 4"
     fill v (xsides `appendSides` box)
  | x' `notElem` nK =  -- assumes x,K subset x',J
      let
        xaux      = unCompAs (lookBox (x,tdir) box) x
        boxprinc  = unFillAs (lookBox (x',dir') box) z
        princnp   = [((z,Up),lookBox (x,tdir') xaux)
                    ,((z, Down), lookBox (x,tdir') box)]
                    ++ auxsides (x',tdir')
        principal = fill (lookBox (x',tdir') tbox) -- tx
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
      in     trace "Kan Fill VU Case 5"
             VFill z (Box tdir x' principal nonprincipal)

  | x' `elem` nK =              -- assumes x,K subset x',J
      let -- surprisingly close to the last case of the Kan-Com-VU filling
        upperbox = unCompAs (lookBox (x,dir') box) x
        npintbox@(Box _ _ _ npintaux) =
          modBox (\zc downside ->
                   let bottom = lookBox zc box
                       top    = lookBox zc upperbox
                       princ  = downside -- same as bottom `face` (x',tdir) and
                                         -- top `face` (x',tdir)
                       sides  = [((z,Down),bottom),((z,Up),top)]
                   in fill (lookBox zc tbox) (Box tdir' x princ -- deg along z!
                                              (sides ++ auxsides zc)))
                 (subBox nK box) -- nK = nK /\ nJ
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
                 ++ map (\(zc,u) -> (zc,u `face` (x',dir))) npintaux
        nplast = ((x',dir),fill (lookBox (x',dir) tbox) (Box Down z nplp nplnp))
      in       trace "Kan Fill VU Case 6"
       VFill z (Box tdir x' principal (nplast:npint))

  where z     = gensym $ support v ++ supportBox box
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

allDirs :: [Name] -> [(Name,Dir)]
allDirs []     = []
allDirs (n:ns) = (n,Down) : (n,Up) : allDirs ns

fills :: [Ter] -> Env -> [Box Val] -> [Val]
fills [] _ []              = []
fills (a:as) e (box:boxes) = v : fills as (Pair e v) boxes
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

-- TODO: Maybe generalize?
appBox :: Box Val -> Box Val -> Box Val
appBox (Box dir x v nvs) (Box _ _ u nus) = Box dir x (app v u) nvus
  where nvus      = [ (nnd,app v (lookup' nnd nus)) | (nnd,v) <- nvs ]
        lookup' x = maybe (error "appBox") id . lookup x

app :: Val -> Val -> Val
app (Ter (Lam t) e) u                           = eval (Pair e u) t
app (Kan Com (VPi a b) box@(Box dir x v nvs)) u =
  trace ("Pi Com:\nufill = " ++ show ufill ++ "\nbcu = " ++ show bcu) com (app b ufill) (appBox box bcu)
  where ufill = fill a (Box (mirror dir) x u [])
        bcu   = cubeToBox ufill (shapeOfBox box)
app kf@(Kan Fill (VPi a b) box@(Box dir i w nws)) v =
  trace ("Pi fill") $ com (app b vfill) (Box Up x vx (((i,Down),vi0) : ((i,Up),vi1):nvs))
  where x     = gensym (support kf `union` support v)
        u     = v `face` (i,dir)
        ufill = fill a (Box (mirror dir) i u [])
        bcu   = cubeToBox ufill (shapeOfBox box)
        vfill = fill a (Box (mirror dir) i u [((x,Down),ufill),((x,Up),v)])
        vx    = fill (app b ufill) (appBox box bcu)
        vi0   = app w (vfill `face` (i,Down))
        vi1   = com (app b ufill) (appBox box bcu)
        nvs   = [ ((n,d),app ws (vfill `face` (n,d))) | ((n,d),ws) <- nws ]
app vext@(VExt x bv fv gv pv) w = com (app bv w) (Box Up y pvxw [((x,Down),left),((x,Up),right)])
  -- NB: there are various choices how to construct this
  where y     = gensym (support vext `union` support w)
        w0    = w `face` (x,Down)
        left  = app fv w0
        right = app gv (swap w x y)
        pvxw  = appName (app pv w0) x
app (Ter (Branch nvs) e) (VCon name us) = case lookup name nvs of
    Just t  -> eval (upds e us) t
    Nothing -> error $ "app: Branch with insufficient "
               ++ "arguments; missing case for " ++ name
app _ _ = error "app"
