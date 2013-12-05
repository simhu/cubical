module Eval where

import Control.Arrow hiding (app)
import Data.List
import Data.Either
import Data.Maybe

import Debug.Trace

import Core

type Name = Integer
type Dim  = [Name]
data Dir  = Up | Down
  deriving (Eq, Show)

mirror :: Dir -> Dir
mirror Up = Down
mirror Down = Up

gensym :: Dim -> Name
gensym [] = 0
gensym xs = maximum xs + 1

-- TODO: merge BoxShape and BoxContent ?
data BoxShape = BoxShape {
  boxDir  :: Dir,  -- direction of the completion (up or down)
  boxName :: Name, -- direction in which to make the completion
  boxDim  :: Dim   -- dimensions of the sides
  }
  deriving (Eq,Show)

data BoxContent = BoxContent {
  boxBottom :: Val,
  boxSides  :: [(Val, Val)]
  }
  deriving (Eq,Show)

boxSide :: BoxContent -> Int -> Dir -> Val
boxSide (BoxContent _ vs) n Down = fst $ vs !! n
boxSide (BoxContent _ vs) n Up   = snd $ vs !! n

lookSide :: BoxShape -> BoxContent -> Name -> Dir -> Val
lookSide (BoxShape bdir bx bdim) (BoxContent b vs) x dir
  | x == bx && mirror bdir == dir = b
  | otherwise = case findIndex (x ==) bdim of
    Just n  -> side $ vs !! n
    Nothing -> error "lookSide" 
  where side = if dir == Up then snd else fst
        
-- assumes the list is of odd size
toBox :: [Val] -> BoxContent
toBox (v:vs) = BoxContent v (pairing vs)
  where pairing [] = []
        pairing (v1:v2:vs) = (v1,v2):pairing vs
        pairing _ = error "toBox: wrong box format (not odd)"
toBox _ = error "toBox: wrong box format (empty box)"

fromBox :: BoxContent -> [Val]
fromBox (BoxContent v vs) = v:foldr (\(v1, v2) ws -> v1:v2:ws) [] vs


-- The pair of values is (down,up)
data Box a = Box Dir Name a [(Name,(a,a))]
  deriving (Eq,Show)

mapBox :: (a -> b) -> Box a -> Box b
mapBox f (Box d n x xs) = Box d n (f x) [ (n',(f down,f up)) | (n',(down,up)) <- xs ]

-- assumes name appears as non principal a direction of the box
lookBox :: Box a -> Name -> Dir -> a
lookBox (Box _ _ _ nvs) x dir = case lookup x nvs of
  Just (down,up) | dir == Up -> up
                 | otherwise -> down
  Nothing -> error $ "lookBox: box not defined on " ++ show x ++ " " ++ show dir

nonPrincipal :: Box a -> [Name]
nonPrincipal (Box _ _ _ nvs) = map fst nvs

instance Functor Box where fmap = mapBox

data KanType = Fill | Com
  deriving (Show, Eq)

data Val = VU
         | Ter Ter Env
         | VId Val Val Val
         | Path Name Val             -- tag values which are paths
         | VExt Name Val Val Val Val -- has dimension (name:dim);
                                         -- vals of dimension dim
         | VPi Val Val
         | VApp Val Val         -- not needed for closed terms
         | VInh Val
         | VInc Val
         | VSquash Name Val Val  -- has dimension (name:dim); vals
                                     -- of dimension dim
         | VCon Ident [Val]
         | Kan KanType Val (Box Val)
         | VLSum [(Ident,[Val])]
         | VEquivEq Name Val Val Val Val Val -- of type U of dimension name:dim
           -- VEquivEq x d a b f s t where
         | VPair Name Val Val -- of type VEquiv
  deriving (Show, Eq)

fstVal, sndVal :: Val -> Val
fstVal (VPair _ a _) = a
fstVal x             = error $ "fstVal: " ++ show x
sndVal (VPair _ _ v) = v
sndVal x             = error $ "fstVal: " ++ show x

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

faceEnv :: Env -> Name -> Dir -> Env
faceEnv e x dir = mapEnv (\u -> face u x dir) e
                          
-- Compute the face map.
-- (i=b) : d -> d-i
face :: Val -> Name -> Dir -> Val
face u x dir =
  let fc v = face v x dir in case u of
  VU          -> VU
  Ter t e     -> ter t (faceEnv e x dir) 
  VId a v0 v1 -> VId (fc a) (fc v0) (fc v1)
  Path y v | x == y    -> u
           | otherwise -> Path y (fc v) 
  VExt y b f g p | x == y && dir == Down -> f
                 | x == y && dir == Up   -> g
                 | otherwise             -> VExt y (fc b) (fc f) (fc g) (fc p)
  VPi a f    -> VPi (fc a) (fc f)
  VApp v0 v1 -> app (fc v0) (fc v1)
  VInh v     -> VInh (fc v)
  VInc v     -> VInc (fc v)
  VSquash y v0 v1 | x == y && dir == Down -> v0
                  | x == y && dir == Up   -> v1
                  | otherwise             -> VSquash y (fc v0) (fc v1)
  VCon c us -> VCon c (map fc us)
  VLSum bs  -> VLSum (map (second (map fc)) bs)
  VEquivEq y a b f s t | x == y && dir == Down -> a
                       | x == y && dir == Up   -> b
                       | otherwise             -> VEquiv y (fc a) (fc b) (fc f) (fc s) (fc t)
  VPair y a v | x == y && dir == Down -> a
              | x == y && dir == Up   -> fc v
              | otherwise             -> VPair y (fc a) (fc v)
  Kan Fill a b@(Box dir' y v nvs)
    | x /= y && x `notElem` nonPrincipal b -> fill (fc a) (fc <$> b)
    | x `elem` nonPrincipal b              -> lookBox b x dir
    | x == y && dir == mirror dir'         -> v
    | otherwise                            -> com a b
  Kan Com a b@(Box dir' y v nvs)
    | x == y                     -> u
    | x `notElem` nonPrincipal b -> com (fc a) (fc <$> b)
    | x `elem` nonPrincipal b    -> face (lookBox b x dir) y dir'



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
support (VApp v1 v2)      = unionsMap support [v1,v2]
support (VCon _ vs)       = unionsMap support vs
support (VLSum xs)        = unions [ unionsMap support vs | (_,vs) <- xs ]
support (VSquash x v0 v1) = [x] `union` unionsMap support [v0,v1]
support (VExt x b f g p)  = [x] `union` unionsMap support [b,f,g,p]
support (Kan Fill a (Box dir n v vns)) = 
  support a `union` [n] `union` support v `union` 
  unions [ [y] `union` unionsMap support [v1,v2] | (y,(v1,v2)) <- vns ]
support (Kan Com a (Box dir n v vns))  = 
  support a `union` support v `union` 
  unions [ [y] `union` unionsMap support [v1,v2] | (y,(v1,v2)) <- vns ]
support (VEquivEq x a b f s t) = [x] `union` unionsMap support [a,b,f,s,t]
support (VPair x a v)          = [x] `union` unionsMap support [a,v]

supportEnv :: Env -> [Name]
supportEnv Empty      = []
supportEnv (Pair e v) = supportEnv e `union` support v
supportEnv (PDef _ e) = supportEnv e

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

swap :: Val -> Name -> Name -> Val
swap u x y = 
  let sw u = swap u x y in case u of
  VU      -> VU
  Ter t e -> Ter t (swapEnv e x y) 
  VId a v0 v1 -> VId (sw a) (sw v0) (sw v1)
  Path z v | z == x    -> u
           | z /= y    -> Path z (sw v)
           | otherwise -> let z' = gensym ([x] `union` [y] `union` support v)
                              v' = swap v z z'
                          in Path z' (sw v')
  VExt z b f g p -> VExt (swapName z x y) (sw b) (sw f) (sw g) (sw p)
  VPi a f -> VPi (sw a) (sw f)
  VApp v0 v1 -> app (sw v0) (sw v1)
  VInh v -> VInh (sw v)
  VInc v -> VInc (sw v)
  VSquash z v0 v1 -> VSquash (swapName z x y) (sw v0) (sw v1)
  VCon c us -> VCon c (map sw us)
  VLSum bs  -> VLSum (map (second (map sw)) bs)
  VEquivEq z a b f s t -> VEquiv (swapName z x y) (sw a) (sw b) (sw f) (sw s) (sw t)
  VPair z a v -> VPair (swapName z x y) (sw a) (sw v)
  Kan Fill a b@(Box dir' z v nvs) ->
    fill (sw a) (Box dir' (swapName z x y) (sw v)
                 [ (swapName n x y,(sw v0,sw v1)) | (n,(v0,v1)) <- nvs ])
  Kan Com a b@(Box dir' z v nvs)
    | z == x    -> u                 -- OK?
    | z /= y    -> com (sw a) (Box dir' (swapName z x y) (sw v)
                     [ (swapName n x y,(sw v0,sw v1)) | (n,(v0,v1)) <- nvs ])
    | otherwise -> let z' = gensym ([x] `union` [y] `union` support u)
                       a' = swap a z z'
--                       v' = swap v 
                   in undefined


eval :: Dim -> Env -> Ter -> Val
eval _ _ U       = VU
eval d e (Var i) = look i d e
eval d e (Id a a0 a1) = VId (eval d e a) (eval d e a0) (eval d e a1)
eval d e (Refl a)  = Path $ eval d e a `res` deg d (gensym d : d)

eval d e (Trans c p t) =
  case eval d e p of
    Path pv -> com (x:d) (app (x:d) (eval (x:d) e' c) pv) box content
    pv -> error $ "eval: trans-case not a path value:" ++ show pv -- ??
  where x = gensym d
        e' = mapEnv (`res` deg d (x:d)) e
        box = BoxShape Up x []
        content = BoxContent (eval d e t) []

eval d e (TransInv c p t) =
  case eval d e p of
    Path pv -> com (x:d) (app (x:d) (eval (x:d) e' c) pv) box content
    pv -> error $ "eval: trans-case not a path value:" ++ show pv -- ??
  where x = gensym d
        e' = mapEnv (`res` deg d (x:d)) e
        box = BoxShape Down x []
        content = BoxContent (eval d e t) []

-- TODO: throw out v, not needed?
eval d e (J a u c w v p) = case eval d e p of
  Path pv ->
    --trace ("J: A: " ++ show (eval dxy exy a) ++ "\n theta:" ++ show theta ++"\n omega: " ++ show omega)
               com dy (app dy (app dy cv omega) sigma) shape valbox
    where
      x = gensym d
      y = gensym (x:d)
      dy = y:d
      z = gensym dy             -- TODO: do we really need z? Can't we
                                -- just 'com' along x?
      dxy = y:x:d
      uv = eval d e u
      ux = uv `res` deg d (x:d)
      uy = uv `res` deg d dy
      exy = mapEnv (`res` deg d dxy) e
      ey = mapEnv (`res` deg d dy) e
      theta = fill dxy (eval dxy exy a)
              (BoxShape Up x [y]) (BoxContent uy [(ux,pv)]) -- y:x:d
      thetaxtoz = theta `res` update (identity dy) x z        -- z:y:d
      sigma = Path thetaxtoz                              -- y:d
      omega = theta `res` face dxy x Up                 -- y:d
      cv = eval dy ey c                                   -- y:d
      shape = BoxShape Up y []
      valbox = BoxContent (eval d e w) []
  pv -> error $ "eval: J on a non path value:" ++ show pv

eval d e (JEq a u c w) = Path $ filled `res` update (identity d) y x
  where
    x = gensym d
    y = gensym (x:d)
    dy = y:d
    z = gensym (y:d)          -- TODO: do we really need z? Can't we
                              -- just 'com' along x?
    dxy = y:x:d
    exy = mapEnv (`res` deg d dxy) e
    ey = mapEnv (`res` deg d dy) e
    uv = eval d e u
    ux = uv `res` deg d (x:d)
    uy = uv `res` deg d dy
    theta = fill dxy (eval dxy exy a)
            (BoxShape Up x [y]) (BoxContent uy [(ux,ux)])
    thetaxtoz = theta `res` update (identity dy) x z
    sigma = Path thetaxtoz
    omega = theta `res` face dxy x Up
    cv = eval dy ey c
    shape = BoxShape Up y []
    valbox = BoxContent (eval d e w) []
    filled = fill dy (app dy (app dy cv omega) sigma) shape valbox

    -- x = gensym d
    -- dx = x:d
    -- wv = eval d e w
    -- uv = eval d e u
    -- reflu = Path $ uv `res` deg d dx
    -- ex = map (`res` (deg d dx) e)
    -- cv = eval dx ex c

eval d e (Ext b f g p) =
  Path $ VExt (gensym d) d (eval d e b) (eval d e f) (eval d e g) (eval d e p)
eval d e (Pi a b)  = VPi (eval d e a) (eval d e b)
eval d e (Lam t)   = Ter (Lam t) e -- stop at lambdas
eval d e (App r s) = app d (eval d e r) (eval d e s)

eval d e (Inh a) = VInh (eval d e a)
eval d e (Inc t) = VInc (eval d e t)
eval d e (Squash r s) = Path $ VSquash (gensym d) d (eval d e r) (eval d e s)
eval d e (InhRec b p phi a) =
  inhrec d (eval d e b) (eval d e p) (eval d e phi) (eval d e a)
eval d e (Where t def) = eval d (PDef def e) t
--  where e' = map (eval d e') (reverse def) ++ e -- use Haskell's laziness
--eval d e (Where t def) = eval d (map (eval d e) def ++ e) t
eval d e (Con name ts) = VCon name (map (eval d e) ts)
-- eval d e (Branch alts) = VBranch alts e
eval d e (Branch alts) = Ter (Branch alts) e
  -- VBranch $ map (\(n,t) -> (n, eval d e t)) alts
eval d e (LSum ntss) = --trace ("eval lsum " ++ show ntss ++ "\n")
                       --  VLSum $ map (\(n,ts) -> (n, map (eval d e) ts)) ntss
                         Ter (LSum ntss) e

eval d e (EquivEq a b f s t) =  -- TODO: are the dimensions of a,b,f,s,t okay?
  Path $ VEquivEq (gensym d) d (eval d e a) (eval d e b)
                  (eval d e f) (eval d e s) (eval d e t)

inhrec :: Dim -> Val -> Val -> Val -> Val -> Val
inhrec d _ _ phi (VInc a) = app d phi a
inhrec d' b p phi (VSquash x d a0 a1) = -- dim. of b,p,phi is x:d
  app d (app d p b0) b1                 -- d' should be x:d
  where fc w dir = res w (face (x:d) x dir)
        b0 = inhrec d (fc b Down) (fc p Down) (fc phi Down) a0
        b1 = inhrec d (fc b Up) (fc p Up) (fc phi Up) a1
--        d' = delete x d
inhrec _ b p phi (Kan ktype d (VInh a) box@(BoxShape dir i d') bc) =
  kan ktype d b box (modBox dir i d' bc irec)
  where  irec dir j v = inhrec (delete j d) (fc b) (fc p) (fc phi) v
           where fc v = res v (face d j dir)
--inhrec b p phi a = VInhRec b p phi a

unPath :: Val -> Val
unPath (Path v) = v
unPath v        = error $ "unPath: " ++ show v

kan :: KanType -> Dim -> Val -> BoxShape -> BoxContent -> Val
kan Fill = fill
kan Com = com

-- Kan filling
fill :: Dim -> Val -> BoxShape -> BoxContent -> Val
fill d (VId a v0 v1) box@(BoxShape dir i d') bc =
--  trace ("Id fill box = " ++ show box ++ "\ntype a= " ++ show a ++ "\n"
--        ++ "v0 = " ++ show v0 ++ "\nv1 = " ++ show v1)
    Path $ fill (x:d) ax (BoxShape dir i (x:d')) (BoxContent vx ((v0, v1):vsx))
  where x   = gensym d            -- i,d' <= d
        ax  = a `res` (deg d (x:d)) -- dim x:d
        BoxContent vx vsx = modBox Up i d' bc
                    (\_ j v -> let dj = delete j d
                                   f  = update (identity dj) (gensym dj) x
                             in unPath v `res` f)
fill d (Ter (LSum nass) e) box bcv = -- assumes cvs are constructor vals
--  trace ("fill sum")
  VCon name ws
  where
    as = case lookup name nass of
           Just as -> as
           Nothing -> error $ "fill: missing constructor "
                      ++ "in labelled sum " ++ name
    name = extractName bcv
    extractName (BoxContent (VCon n _) _) = n
    extractName x = error "fill VLSum: not a constructor (bottom)"
    extractArgs = map (\v -> case v of
                          VCon n xs | n == name -> xs
                          VCon n _ -> error $ "fill VLSum: constructors " ++ n ++
                               " and " ++ name ++ " do not match"
                          _ -> error "fill VLSum: not a constructor (side)"
                      )
    argboxes = map toBox $ transpose $ extractArgs $ fromBox bcv
    -- fill boxes for each argument position of the constructor
    ws = fills d as e box argboxes
    err x = error $ "fill: not applied to constructor expressions " ++ show x
fill d (VEquivEq x d' a b f s t) bs@(BoxShape dir z dJ) bc@(BoxContent vz vJ) 
  | x /= z && x `notElem` dJ =
    -- d == x : d' ?!
    let ax0  = fill d' a bs (modBox dir z dJ bc (\dy ny vy -> fstVal vy))
        bx0  = app d' f ax0
        bcx1 = modBox dir z dJ bc (\dy ny vy -> sndVal vy `res` face d x Up)
        BoxContent bz bJ = modBox dir z dJ bc (\dy ny vy -> sndVal vy)
        bx1  = fill d' b bs bcx1
        v    = fill d (b `res` deg d' d)
                   (BoxShape dir z (x : dJ)) (BoxContent bz ((bx0,bx1) : bJ))
    in trace "VEquivEq case 1" $ VPair x ax0 v
  | x /= z && x `elem` dJ =
    let ax0 = lookSide bs bc x Down
        -- TODO: Clean
        bz  = modBox dir z dJ bc (\dy ny vy -> if x /= ny then sndVal vy else
                                                 if dy == Down then app d' f ax0 else vy)
        v   = fill d (b `res` deg d' d) bs bz
    in trace "VEquivEq case 2" $ VPair x ax0 v
  | x == z && dir == Up =
    let ax0 = lookSide bs bc x Down
        bx0 = app d' f ax0
        bJ  = map (\(x,y) -> (sndVal x,sndVal y)) vJ
        -- TODO: Add a layer of abstraction for that
        v   = fill d (b `res` deg d' d) bs (BoxContent bx0 bJ) 
    in trace "VEquivEq case 3" $ VPair x ax0 v
  | x == z && dir == Down =
    let y  = gensym d
        b  = vz
        sb = app d' s b
        gb = vfst sb
        BoundaryContent abnd = modBoundary d' (BoundaryContent vJ)
                                 (\dz nz vz -> fst (vpairToSquare dz nz vz))

        BoundaryContent bbnd = modBoundary d' (BoundaryContent vJ)
                                 (\dz nz vz -> snd (vpairToSquare dz nz vz))                               
        aboxshape = BoxShape Up y d'
        abox  = BoxContent gb abnd
        afill = fill (y:d') (a `res` deg d' (y : d')) aboxshape abox
        acom  = com (y:d') (a `res` deg d' (y : d')) aboxshape abox
        fafill = app (y : d') (f `res` deg d' (y : d')) afill
        sbsnd = rename d' (unPath (vsnd sb)) (gensym d') x
        degb  = b `res` deg d' (y : d')

        bboxshape = BoxShape Up y (x:d')
        bbox = BoxContent sbsnd ((fafill,degb) : bbnd)
        bcom = com (y : d) (b `res` deg d' (y : d)) bboxshape bbox
        -- TODO: Introduce pathWith?
        vpairToSigma :: Name -> Val -> Val
        vpairToSigma z (VPair _ a0 v0) =
          VCon "pair" [a0,Path $ rename (delete z d) v0 x (gensym (delete z d'))]
        -- TODO: Permute name and dir  
        vpairToSquare :: Dir -> Name -> Val -> (Val,Val)
        vpairToSquare dir z vp@(VPair _ a0 v0) =
          let t0   = t `res` face d' z dir
              b0   = b `res` face d' z dir
              d'z  = delete z d'
              gd'z = gensym d'z
              d''  = gd'z : d'z
              gd'' = gensym d''
              -- TODO: Write unPathAs and pathWith
              VCon "pair" [l0,sq0] =
                unPath $ app d'z (app d'z t0 b0) (vpairToSigma z vp)
              l0'  = rename d'z l0 (gensym d'z) y
              (fstsq0,sndsq0) = (vfst sq0,unPath $ vsnd sq0)
          in (rename d'z fstsq0 gd'z x,
              rename d'' (rename d'z sndsq0 gd'z x) gd'' y)
        
    in trace "VEquivEq case 4" $ VPair x acom bcom
  | otherwise = error "fill EqEquiv"    
fill d v b vs = Kan Fill d v b vs


-- Given C : B -> U such that s : (x : B) -> C x and
-- t : (x : B) (y : C x) -> Id (C x) (s x) y, we construct
-- a filling of closed empty cube (i.e., the boundary
-- of a cube) over a cube u in B.
-- C b = sigma (a : A) (Id B (f a) b)

-- fillBoundary :: Dim -> Val -> Val -> Val -> Val -> Val -> BoundaryShape -> BoundaryContent -> Val
-- fillBoundary d b c s t u bs@(BoundaryShape d') bc@(BoundaryContent vs) =
-- fill d (VEquivEq x d' a b f s t) bs@(BoxShape dir z dJ) bc@(BoxContent vz vJ) 


-- is this sigma?
vsigma :: Val -> Val -> Val
vsigma a b =
  Ter (LSum [("pair",[Var 1,App (Var 1) (Var 0)])]) (Pair (Pair Empty a) b) 

vpair :: Val -> Val -> Val
vpair a b = VCon "pair" [a,b]

vfst, vsnd :: Val -> Val
vfst (VCon "pair" [a,b]) = a
vfst _ = error "vfst"
vsnd (VCon "pair" [a,b]) = b
vsnd _ = error "vsnd"



fills :: Dim -> [Ter] -> Env -> BoxShape -> [BoxContent] -> [Val]
fills _ [] _ _ [] = []
fills d (a:as) e box (bc:bcs) = v : fills d as (Pair e v) box bcs
  where v = fill d (eval d e a) box bc
fills _ _ _ _ _ = error "fills: different lengths of types and values"

-- Composition (ie., the face of fill which is created)
-- Note that the dimension is not the dimension of the output value,
-- but the one where the open box is specified
com :: Dim -> Val -> BoxShape -> BoxContent -> Val
com d (VId a v0 v1) box@(BoxShape dir i d') bc =
--  trace ("Id com box = " ++ show box ++ "\ntype a= " ++ show a ++ "\n"
--        ++ "v0 = " ++ show v0 ++ "\nv1 = " ++ show v1)
    res (fill d (VId a v0 v1) (BoxShape dir i d') bc) (face d i dir)
    -- face d i dir is (i=dir): d -> d-i
com d (Ter (LSum nass) e) (BoxShape dir i d') bc =
  res (fill d (Ter (LSum nass) e) (BoxShape dir i d') bc) (face d i dir)
-- com d (VEquivEq x d a b f s t) bs@(BoxShape dir z dJ) bc@(BoxContent vz vJ) 
--   | x /= z && x `notElem` dJ =
--     let ax0  = fill d a bs (modBox dir z dJ bc (\dy ny vy -> fstVal vy))
--         bx0  = app d f ax0
--         bcx1 = modBox dir z dJ bc (\dy ny vy -> sndVal vy `res` face d x Up)
--         BoxContent bz bJ = modBox dir z dJ bc (\dy ny vy -> sndVal vy)
--         bx1  = fill d b bs bzx1
--         v    = fill (x : d) (b `res` deg d (x : d))
--                    (BoxShape dir z (x : dJ)) (BoxContent bz ((bx0,bx1) : bJ))
--     in VPair x ax0 v
com d (VEquivEq x d' a b f s t) bs@(BoxShape dir z dJ) bc =
  fill d (VEquivEq x d' a b f s t) bs bc `res` face d z dir
    
com d v b bc = Kan Com d v b bc



app :: Dim -> Val -> Val -> Val
app d (Ter (Lam t) e) u = eval d (Pair e u) t
app d (Kan Com bd (VPi a b) box@(BoxShape dir i d') bcw) u = -- here: bd = i:d
--  trace ("Pi com box=" ++ show box ++ " \n" ++ "ufill " ++ show ufill)
    com bd (app bd b ufill) box bcwu
  where ufill = fill bd a (BoxShape (mirror dir) i []) (BoxContent u [])
        bcu = cubeToBox ufill bd box
        bcwu = appBox bd box bcw bcu
app d (Kan Fill bd (VPi a b) box@(BoxShape dir i d') bcw) v = -- here: bd = d
  trace ("Pi fill\n") com (x:d) (app (x:d) bx vfill) (BoxShape Up x (i:d')) wvfills
  where x = gensym d            -- add a dimension
        ax = res a (deg d (x:d))
        bx = res b (deg d (x:d))
        di = delete i d         -- d minus i !!
        u = res v (face d i dir)
        ufill = fill d a (BoxShape (mirror dir) i []) (BoxContent u [])
        -- cut an (i,d')-open box (in dir) from ufill
        bcu = cubeToBox ufill d box
        ux = res u (deg di (x:di)) -- dim. x:(d-i)
        -- (i,[x])-open box in x:d (some choice on the order..) (mirror dir)
        bcv = BoxContent ux [(ufill,v)]
        vfill = fill (x:d) ax (BoxShape (mirror dir) i [x]) bcv
        vbox = cubeToBox vfill (x:d) box
        bcwx = resBox i d' bcw (deg d (x:d))
        BoxContent wuimdir wbox' = appBox (x:d) box bcwx vbox
        -- the missing faces to get a (x, i:d')-open box in x:i:d (dir)
        wux0 = fill d (app d b ufill) box (appBox d box bcw bcu)
        wuidir = res (app (x:di) (com d (VPi a b) box bcw) u) (deg di (x:di))
        -- arrange the i-direction in the right order
        wuis = if dir == Up then (wuidir,wuimdir) else (wuimdir,wuidir)
        -- final open box in (app bx vsfill)
        wvfills = BoxContent wux0 (wuis:wbox')
app d (VExt x d' bv fv gv pv) w = -- d = x:d'; values in vext have dim d'
  com (y:d) (app (y:d) bvxy wy) (BoxShape Up y [x]) (BoxContent pvxw [(left,right)])
  -- NB: there are various choices how to construct this
  where y = gensym d
        bvxy = res bv (deg d' (y:d))
        wy = res w (deg d (y:d))
        w0 = res w (face d x Down)
        dg = deg d' (y:d')
        left = res (app d' fv w0) dg
        wxtoy = res w (update (identity d') x y)
        right = app (y:d') (res gv dg) wxtoy
        pvxw = unPath $ app d' pv w0
-- app d (VBranch alts e) (VCon name us) =
--   case lookup name alts of
--     Just t -> eval d (reverse us ++ e) t
--     Nothing -> error $ "app: VBranch with insufficient "
--                ++ "arguments; missing case for " ++ name
-- app d (VBranch nvs) (VCon name us) =
--   case lookup name nvs of
--     Just v -> apps d v us
--     Nothing -> error $ "app: VBranch with insufficient "
--                ++ "arguments; missing case for " ++ name
app d (Ter (Branch nvs) e) (VCon name us) =
  case lookup name nvs of
    Just t -> eval d (upds e us) t
    Nothing -> error $ "app: Branch with insufficient "
               ++ "arguments; missing case for " ++ name
app d u v = VApp u v            -- error ?

apps :: Dim -> Val -> [Val] -> Val
apps d v [] = v
apps d v (u:us) = apps d (app d v u) us
-- TODO: rewrite as foldl(?r) (app d) v

-- TODO: QuickCheck!
prop_resId :: Val -> Mor -> Bool
prop_resId v f = res v (identity (cod f)) == v

-- TODO: express in haskell?
-- v is a cube in dimension dom f ==> res v f is a cube in dimension cod f

-- findName :: (Name -> Bool) -> Dim -> Maybe Name
-- findName _ [] = Nothing
-- findName f (x:xs) | f x = Just x
-- findName f (_:xs) | otherwise = findName f xs

res :: Val -> Mor -> Val
res VU _ = VU
res (VId v v0 v1) f = VId (res v f) (res v0 f) (res v1 f)
res (Path v) f = Path $ res v (update f (gensym $ dom f) (gensym $ cod f))
res (VPi a b) f = VPi (res a f) (res b f)
-- res (Ter t e) f = eval (cod f) (mapEnv (`res` f) e) t
res (Ter t e) f = Ter t (mapEnv (`res` f) e) -- should be the same as above
res (VApp u v) f = app (cod f) (res u f) (res v f)
-- res (Res v g) f = res v (g `comp` f)
res (Kan Fill d u (BoxShape dir i d') (BoxContent v _)) f | (f `ap` i) `direq` mirror dir =
  res v (f `minus` i)
res (Kan Fill d u shape@(BoxShape dir i d') bc) f | (f `ap` i) `direq` dir =
  res (Kan Com d u shape bc) (f `minus` i) -- This will be a Com
--  com (cod f) (res u f) (resShape shape f) (resBox i d' bc f) -- (f `minus` i))
res (Kan Fill d u (BoxShape dir i d') bc) f | isJust cand =
  res v (f `minus` j)
  -- TODO: CLEAN!
  where cand      = findIndex (\j -> j `elem` ndef f) d'
        n         = fromJust cand
        j         = d' !! n
        -- cand = findName (\j -> j `elem` ndef f) d'
        -- j = fromJust cand
        Left dir  = f `ap` j
        v         = boxSide bc n dir
res (Kan Fill d u shape@(BoxShape dir i d') bc) f | (i:d') `subset` def f = -- otherwise?
  fill (cod f) (res u f)
       (resShape shape f)
--       (BoxShape dir (f `dap` i) (map (f `dap`) d'))
       (resBox i d' bc f)
res (Kan Fill d u (BoxShape dir i d') vs) f = error $ "Fill: not possible? i="
                                              ++ show i ++ "d' = " ++ show d'
                                              ++ "f = " ++ show f ++ " d= " ++ show d
res (Kan Com d u (BoxShape dir i d') bc) f | isJust cand =
  res v (g `minus` j)
  where cand = findIndex (\j -> j `elem` ndef f) d'
        n         = fromJust cand
        j         = d' !! n
        Left dir  = f `ap` j
        v         = boxSide bc n dir -- dim. d-j
        g         = face d i dir `comp` f
res (Kan Com d u shape@(BoxShape dir i d') bc) f | d' `subset` def f =
  com co (res u fupd) (resShape shape fupd) (resBox i d' bc fupd)
  where co = cod f
        i' = gensym co
        fupd = update f i i'
res (Kan Com d u (BoxShape dir i d') bc) f = error $  "Com: not possible? i="
                                             ++ show i ++ "d' = " ++ show d'
                                             ++ "f = " ++ show f ++ " d= " ++ show d
-- res (Kan Com d u (BoxShape dir i d') bc) f = -- here: i:dom f = d
--   trace "res com" (res (res (fill d u (BoxShape dir i d') bc) g) ytodir)
--   where x = gensym d
--         co = cod f
--         y = gensym co
--         itox = update (identity (dom f)) i x -- (i=x):d->(d-i),x
--         fxtoy = update f x y -- (f,x=y):(d-i),x -> co,y
--         ytodir = face (y:co) y dir   -- (y=dir):co,y -> co
--         -- note that: (i=dir) f = (i=x) (f,x=y) (y=dir)
--         g = itox `comp` fxtoy   -- defined on x, hence non-circular call to res
--             -- g : d -> co, y has i in def g
res (VExt x d bv fv gv pv) f | x `elem` def f = -- dom f = x:d
  VExt (f `dap` x) d' (bv `res` fminusx) (fv `res` fminusx) (gv `res` fminusx)
       (pv `res` fminusx)
  where fminusx = f `minus` x
        d' = cod fminusx
res (VExt x d bv fv gv pv) f | (f `ap` x) `direq` Down = fv `res` (f `minus` x)
res (VExt x d bv fv gv pv) f | (f `ap` x) `direq` Up = gv `res` (f `minus` x)
res (VInh v) f = VInh (res v f)
res (VInc v) f = VInc (res v f)
res (VSquash x d u v) f | x `elem` def f = -- dom f = x:d
  VSquash (f `dap` x) d' (res u fminusx) (res v fminusx)
  where -- f-x : d -> d' ; f : x:d -> cod f;
        fminusx = f `minus` x
        d' = cod fminusx
res (VSquash x d u v) f | x `elem` dom f && (f `ap` x) `direq` Down = res u (f `minus` x)
res (VSquash x d u v) f | x `elem` dom f && (f `ap` x) `direq` Up = res v (f `minus` x)
res (VSquash x d u v) f = error $ "Vsquash impossible d= " ++ show d ++ " f = " ++ show f
--res (VInhRec b p phi a) f = inhrec (res b f) (res p f) (res phi f) (res a f)
--res (VBranch alts) f = VBranch $ map (\(n,v) -> (n,  res v f)) alts
res (VCon name vs) f = VCon name (map (`res` f) vs)
--res (VLSum nass) f = VLSum $ map (\(n,as) -> (n, map (`res` f) as)) nass

res (VEquivEq x d a b g s t) f | x `elem` def f =
  VEquivEq (f `dap` x) (cod f) (a `res` h) (b `res` h) (g `res` h)
           (s `res` h) (t `res` h)
   where h = f `minus` x
res (VEquivEq x d a b g s t) f | f `ap` x `direq` Down =
  a `res` (f `minus` x)
res (VEquivEq x d a b g s t) f | f `ap` x `direq` Up =
  b `res` (f `minus` x)
-- res (VEquivEq x d a b g s t) f = error "VEquivEq impossible"

res (VPair x a v) f | x `elem` def f =
  VPair (f `dap` x) (a `res` h) (v `res` f)
   where h = f `minus` x
res (VPair x a v) f | f `ap` x `direq` Down =
  a `res` (f `minus` x)
res (VPair x a v) f | f `ap` x `direq` Up =
  v `res` f

res p f = error $ "res: " ++ show p ++ " " ++ show f
  -- res v f = Res v f
--res _ _ = error "res: not possible?"

-- Takes a u and returns an open box u's given by the specified faces.
cubeToBox :: Val -> Dim -> BoxShape -> BoxContent
cubeToBox u d (BoxShape dir i d') =
  BoxContent (get i dir) [ (get j Down, get j Up) | j <- d']
  where get j dir = res u (face d j dir)

-- Apply an open box of functions of a given shape to a corresponding
-- open box of arguments.
appBox :: Dim -> BoxShape -> BoxContent -> BoxContent -> BoxContent
appBox d (BoxShape _ i d') (BoxContent w ws) (BoxContent u us) =
  BoxContent (get i w u) [(get j w1 u1, get j w2 u2)
                         | ((w1, w2), (u1, u2), j) <- zip3 ws us d']
  where get j = app (delete j d)

modBox :: Dir -> Name -> Dim -> BoxContent -> (Dir -> Name -> Val -> Val) -> BoxContent
modBox dir i d (BoxContent v vs) f =
  BoxContent (f dir i v) (zipWith (\j (v, w) -> (f Down j v, f Up j w)) d vs)

-- (box i d vs) f
-- i  = what we fill along
-- d  = dimension
-- vs = open box
resBox :: Name -> Dim -> BoxContent -> Mor -> BoxContent
resBox i d bc f = modBox Up i d bc (\_ j v -> res v (f `minus` j))

-- assumes f is defined on i:d'
resShape :: BoxShape -> Mor -> BoxShape
resShape (BoxShape dir i d') f =
  BoxShape dir (f `dap` i) (map (f `dap`) d')

subset :: Eq a => [a] -> [a] -> Bool
subset xs ys = all (`elem` ys) xs


-- Given B : A -> U such that s : (x : A) -> B x and
-- t : (x : A) (y : B x) -> Id (B x) (s x) y, we construct
-- a filling of closed empty cube (i.e., the boundary
-- of a cube) over a cube u in A.

fillBoundary :: Dim -> Val -> Val -> Val -> Val -> Val -> BoundaryShape -> BoundaryContent -> Val
fillBoundary d a b s t u bs@(BoundaryShape d') bc@(BoundaryContent vs) =
  com xd (app xd bx ux) (BoxShape Up x d') (BoxContent (app d s u) rest)
  where x    = gensym d
        xd   = x:d
        bx   = b `res` deg d xd   -- TODO: can be "b"
        ux   = u `res` deg d xd   -- can be "u"
        tbnd = cubeToBoundary t d bs
        tbc  = appBoundary d bs tbnd bc
        BoundaryContent rest = modBoundary d' tbc
                                (\ _ n v -> let nd = delete n d in
                                  rename nd (unPath v) (gensym nd) x)

-- rename x to y in v. assumes x and y are fresh to d.
rename :: Dim -> Val -> Name -> Name -> Val
rename d v x y = v `res` update (identity d) x y

-- fillBoundary :: Dim -> Val -> Val -> Val -> Val -> Val -> BoundaryShape -> BoundaryContent -> Val
-- fillBoundary d a b s t u bs@(BoundaryShape d') bc@(BoundaryContent vs) =
--   com xd (app xd bx ux) (BoxShape Up x d') (BoxContent (app d s u) rest)
--   where x    = gensym d
--         xd   = x:d
--         bx   = b `res` deg d xd   -- TODO: can be "b"
--         ux   = u `res` deg d xd   -- can be "u"
--         tbnd = cubeToBoundary t d bs
--         tbc  = appBoundary d bs tbnd bc
--         BoundaryContent rest = modBoundary d' tbc
--                                 (\ _ n v -> let nd = delete n d in
--                                   unPath v `res` update (identity nd) (gensym nd) x)


data BoundaryShape = BoundaryShape {
  boundaryDim  :: Dim
  }
  deriving (Eq,Show)

data BoundaryContent = BoundaryContent {
  boundarySides  :: [(Val, Val)]
  }
  deriving (Eq,Show)

boundarySide :: BoundaryContent -> Int -> Dir -> Val
boundarySide (BoundaryContent vs) n Down = fst $ vs !! n
boundarySide (BoundaryContent vs) n Up  = snd $ vs !! n

-- assumes the list is of even size
toBoundary :: [Val] -> BoundaryContent
toBoundary vs = BoundaryContent (pairing vs)
  where pairing [] = []
        pairing (v1:v2:vs) = (v1,v2):pairing vs
        pairing _ = error "toBoundary: wrong boundary format (not even)"

fromBoundary :: BoundaryContent -> [Val]
fromBoundary (BoundaryContent vs) = foldr (\(v1, v2) ws -> v1:v2:ws) [] vs


-- Takes a u and returns the boundary u's given by the specified faces.
cubeToBoundary :: Val -> Dim -> BoundaryShape -> BoundaryContent
cubeToBoundary u d (BoundaryShape d') =
  BoundaryContent [ (get j Down, get j Up) | j <- d']
  where get j dir = res u (face d j dir)

-- Apply an open boundary of functions of a given shape to a corresponding
-- open boundary of arguments.
appBoundary :: Dim -> BoundaryShape -> BoundaryContent -> BoundaryContent -> BoundaryContent
appBoundary d (BoundaryShape d') (BoundaryContent ws) (BoundaryContent us) =
  BoundaryContent [(get j w1 u1, get j w2 u2)
                  | ((w1, w2), (u1, u2), j) <- zip3 ws us d']
  where get j = app (delete j d)

modBoundary :: Dim -> BoundaryContent -> (Dir -> Name -> Val -> Val) -> BoundaryContent
modBoundary d (BoundaryContent vs) f =
  BoundaryContent (zipWith (\j (v, w) -> (f Down j v, f Up j w)) d vs)

resBoundary :: Dim -> BoundaryContent -> Mor -> BoundaryContent
resBoundary d bc f = modBoundary d bc (\_ j v -> res v (f `minus` j))

-- assumes f is defined on d'
resBoundaryShape :: BoundaryShape -> Mor -> BoundaryShape
resBoundaryShape (BoundaryShape d') f =
  BoundaryShape (map (f `dap`) d')
