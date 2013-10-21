module Eval where

import Data.List
import Data.Either
import Data.Maybe
import Text.Printf

import Core

type Name = Integer
type Dim  = [Name]
type Dir  = Bool

dimeq :: Dim -> Dim -> Bool
dimeq d d' = sort (nub d) == sort (nub d')

gensym :: Dim -> Name
gensym xs = maximum xs + 1

-- all *very* hackish
type Mor = ([(Name, Either Dir Name)], Dim)
-- I -> J u {0,1}

identity :: Dim -> Mor
identity d = ([(i, Right i) | i <- d], d)

dom :: Mor -> Dim               -- *not* the names f is defined on
dom (al,cd) = map fst al

cod :: Mor -> Dim
cod (al,co) = co

def :: Mor -> Dim
def (al, co)  = [ i | (i, Right _) <- al ]

ndef :: Mor -> Dim
ndef (al, co) = [ i | (i, Left _) <- al ]

-- update f xs ys is (f, xs=ys) (xs and ys fresh)
update :: Mor -> [Name] -> [Name] -> Mor
update (al,co) xs ys = (al', co ++ ys)
  where al' = al ++ zipWith (\x y -> (x, Right y)) xs ys

im :: Mor -> Dim
im (al, _) = [ y | (_, Right y) <- al ]

ap :: Mor -> Name -> Either Dir Name
f@(al, _) `ap` i = case lookup i al of
  Just x    -> x
  otherwise -> error $ printf "ap: %s undefined on %s" (show f) (show i)

-- Supposes that f is defined on i
dap :: Mor -> Name -> Name
f `dap` i = case f `ap` i of
  Left b -> error "dap: undefined"
  Right x -> x

comp :: Mor -> Mor -> Mor -- use diagram order!
comp f g = ([(i, (f `ap` i) >>= (g `ap`))| i <- dom f], cod g)

-- Assumption: d <= c
-- Compute degeneracy map.
deg :: Dim -> Dim -> Mor
deg d c = (map (\i -> (i, Right i)) d, c)

-- Compute the face map.
-- (i=b) : d -> d-i
face :: Dim -> Name -> Dir -> Mor
face d i b = ((i, Left b):[(j, Right j) | j <- di], di)
  where di = delete i d

-- If f : I->J and f defined on x, then (f-x): I-x -> J-fx
-- If f : I->J and f not defined on x, then (f-x): I-x -> J
minus :: Mor -> Name -> Mor
(f@(al,co)) `minus` i = ([(j,v)| (j,v) <- al, i/=j] , co')
  where co' | i `elem` dom f = delete (f `dap` i) co
            | otherwise = co

data Box = Box Dir Name Dim -- for x, J; no I (where x,J subset I)
  deriving (Eq,Show)

-- TODO: Type for box content? (a,[(a,a)]) ??

-- data Dir = Up | Down
--          deriving (Eq,Show)

-- True = Up; False = Down

mirror :: Dir -> Dir
mirror = not
-- mirror Up = Down
-- mirror Down = Up

direq :: Either Dir Name -> Dir -> Bool
Left False `direq` False = True
Left True `direq` True = True
_ `direq` _ = False

data Val = VN | VZ | VS Val | VRec Val Val Val
         | Ter Ter Env
         | VId Val Val Val      -- ??
         | Path Val             -- tag values which are paths
--         | VTrans Val Val Val   -- ?? needed
         | VPi Val Val
         | VApp Val Val
         | VSigma Val Val | VPair Val Val
         | VP Val | VQ Val      -- ??
         | Com Dim Val Box [Val]
         | Fill Dim Val Box [Val]   -- enough?
         | Res Val Mor
  deriving (Show, Eq)

-- An open box (the list of Val's in Com and Fill) is organized as
-- follows: if the Box is (Box dir i [i1,i2,..,in]), then the value vs
-- are [v0,v10,v11,v20,v21,..,vn0,vn1] (2n+1 many) where v0 is of dim
-- d-i and vjb of dim d-ij.

-- This is ugly!
-- instance Show Val where
--   show VN     = "N"
--   show VZ     = "0"
--   show (VS x) = "S (" ++ show x ++ ")"
--   show (VRec v1 v2 v3) = "VRec (" ++ show v1 ++ ") (" ++ show v2 ++ ") (" ++ show v3 ++ ")"
--   show (Ter t e)       = "Ter (" ++ show t ++ ") (" ++ show e ++ ")"
--   show (VId v1 v2 v3)  = "VId (" ++ show v1 ++ ") (" ++ show v2 ++ ") (" ++ show v3 ++ ")"
--   show (Path x)        = "Path (" ++ show x ++ ")"
--   show (VPi v1 v2)     = "VPi (" ++ show v1 ++ ") (" ++ show v2 ++ ")"
--   show (VApp v1 v2)    = "VApp (" ++ show v1 ++ ") (" ++ show v2 ++ ")"
--   show (Com d v b vs)  = "Com (" ++ show d ++ ") (" ++ show v ++ ") (" ++ show b ++ ") (" ++ show vs ++ ")"
--   show (Fill d v b vs) = "Fill (" ++ show d ++ ") (" ++ show v ++ ") (" ++ show b ++ ") (" ++ show vs ++ ")"
--   show (Res v m)       = "Res (" ++ show v ++ ") (" ++ show m ++ ")"

type Env = [Val]

eval :: Dim -> Val -> Val
eval d (Ter t e) = eval' d e t

eval' :: Dim -> Env -> Ter -> Val
eval' d e (Var i) = e !! i
eval' _ _ N       = VN
eval' _ _ Z       = VZ
eval' d e (S t)   = VS (eval' d e t)
eval' d e (Rec tz ts tn) = rec d (eval' d e tz) (eval' d e ts) (eval' d e tn)
eval' d e (Id a a0 a1) = VId (eval' d e a) (eval' d e a0) (eval' d e a1)
eval' d e (Refl a)  = Path $ res (eval' d e a) (deg d (gensym d : d))
eval' d e (Trans c p t) =
  case eval' d e p of
    Path pv -> com (x:d) (eval' (x:d) (pv:e') c) box [eval' d e t]
    pv -> error $ "eval': trans-case not a path value:" ++ show pv -- ??
  where x = gensym d
        e' = map (`res` deg d (x:d)) e
        box = Box True x []
eval' d e (Pi a b)  = VPi (eval' d e a) (eval' d e b)
eval' d e (Lam t)   = Ter (Lam t) e -- stop at lambdas
eval' d e (App r s) = app d (eval' d e r) (eval' d e s)
eval' d e (Sigma a b) = VSigma (eval' d e a) (eval' d e b)
eval' d e (Pair r s) = pair (eval' d e r) (eval' d e s)
eval' d e (P r) = p (eval' d e r)
eval' d e (Q r) = q (eval' d e r)

p :: Val -> Val
p (VPair v w) = v
p v = VP v

q :: Val -> Val
q (VPair v w) = w
q v = VQ v

pair :: Val -> Val -> Val
-- no surjective pairing for now
--pair (VP v) (VQ v') | v == v' = v
pair v w = VPair v w

unPath :: Val -> Val
unPath (Path v) = v
unPath v        = error $ "unPath: " ++ show v

fill :: Dim -> Val -> Box -> [Val] -> Val
fill d VN (Box _ n _) vs = -- head vs
  res (head vs) (deg (delete n d) d)  -- "trivial" filling for nat
fill d (VId a v0 v1) (Box dir i d') vs =
  Path $ fill (x:d) ax (Box dir i (x:d')) (vx:v0x:v1x:vsx)
  where x   = gensym d   -- i,d' <= d
        ax  = res a (deg d (x:d))     -- A(d,x)
--        v0x = res v0 (deg d (x:d))  -- A(d,x)
--        v1x = res v1 (deg d (x:d))  -- A(d,x)
        v0x = v0                      -- A(d)
        v1x = v1                      -- A(d)
        (vx:vsx) = modBox i d' (map unPath vs)
                    (\j -> let dj = delete j d
                           in update (identity dj) [gensym dj] [x])
fill d (VSigma va vb) box vs = fill d (app d vb a) box bs
  where as = map p vs
        bs = map q vs
        a = fill d va box as
fill d v b vs = Fill d v b vs

-- composition
-- Note that the dimension is not the dimension of the output value,
-- but the one where the open box is specified
com :: Dim -> Val -> Box -> [Val] -> Val
com d VN (Box dir i d') vs = head vs
com d (VId a v0 v1) (Box dir i d') vs = -- should actually work (?)
  res (fill d (VId a v0 v1) (Box dir i d') vs) (face d i dir)
com d (VSigma va vb) (Box dir i d') vs = -- should actually work (?)
  res (fill d (VSigma va vb) (Box dir i d') vs) (face d i dir)
com d v b vs = Com d v b vs

-- Takes a u and returns an open box u's given by the specified faces.
cubeToBox :: Val -> Dim -> Box -> [Val]
cubeToBox u d (Box dir i d') = [ res u (face d j b) | (j,b) <- boxshape ]
  where boxshape = (i,dir) : zip dd' (cycle [True,False])
        dd' = concatMap (\j -> [j,j]) d'

-- Apply an open box of functions of a given shape to a corresponding
-- open box of arguments.
appBox :: Dim -> Box -> [Val] -> [Val] -> [Val]
appBox d (Box _ i d') ws us =
  [ app (delete j d) w u | (w,u,j) <- zip3 ws us idd' ]
  where idd' = i : concatMap (\j -> [j,j]) d'

app :: Dim -> Val -> Val -> Val
app d (Ter (Lam t) e) u = eval' d (u:e) t
app d (Com bd (VPi a b) box@(Box dir i d') ws) u = -- here: bd = i:d
  com bd (app bd b ufill) box wus
  where ufill = fill bd a (Box (mirror dir) i []) [u]
        us = cubeToBox ufill bd box
        wus = appBox d box ws us
app d (Fill bd (VPi a b) box@(Box dir i d') ws) v = -- here: bd = d
  com (x:d) (app (x:d) bx vsfill) (Box True x (i:d')) wvfills
  where x = gensym d            -- add a dimension
        ax = res a (deg d (x:d))
        bx = res b (deg d (x:d))
        di = delete i d         -- d minus i !!
        u = res v (face d i dir)
        ufill = fill d a (Box (mirror dir) i []) [u] -- or: Fill? res computes!
        ux = res u (deg di (x:di))                   -- dim. x:(d-i)
        -- (i,[x])-open box in x:d (some choice on the order..) (mirror dir)
        vs = [ux,ufill,v]
        vsfill = fill (x:d) ax (Box (mirror dir) i [x]) vs
        vbox = cubeToBox vsfill (x:d) box
        wsx = resBox i d' ws (deg d (x:d))
        (wuimdir:wsbox') = appBox (x:d) box wsx vbox
        -- cut an (i,d')-open box (in dir) from ufill
        us = cubeToBox ufill d box
        -- the missing faces to get a (x, i:d')-open box in x:i:d (dir)
        wux0 = fill d (app d b ufill) box (appBox d box ws us)
        wuidir = res (app (x:di) (com d (VPi a b) box ws) u) (deg di (x:di))
        -- arrange the i-direction in the right order
        wuis = if dir then [wuidir,wuimdir] else [wuimdir,wuidir]
        -- final open box in (app bx vsfill)
        wvfills = wux0:wuis++wsbox'
app d u v = VApp u v            -- error ?

-- TODO: QuickCheck!
prop_resId :: Val -> Mor -> Bool
prop_resId v f = res v (identity (cod f)) == v

-- TODO: express in haskell?
-- v is a cube in dimension dom f ==> res v f is a cube in dimension cod f

res :: Val -> Mor -> Val
-- res v f | f == identity (cod f) = v   -- why? not needed?
res VN _ = VN                   -- or catch all consts in the end?
res VZ _ = VZ
res (VS v) f = VS (res v f)
res (VRec vz vs v) f = rec (cod f) (res vz f) (res vs f) (res v f) -- ??
res (VId v v0 v1) f = VId (res v f) (res v0 f) (res v1 f)
res (Path v) f = Path $ res v (update f [gensym $ dom f] [gensym $ cod f])
res (VPi a b) f = VPi (res a f) (res b f)
res (Ter t e) f = eval' (cod f) (map (`res` f) e) t  -- t is a lambda?
res (VApp u v) f = app (cod f) (res u f) (res v f)
res (VSigma a b) f = VSigma (res a f) (res b f)
res (VPair r s) f = pair (res r f) (res s f)
res (VP r) f = p (res r f)
res (VQ r) f = q (res r f)
res (Res v g) f = res v (g `comp` f)   -- right order for comp???
res (Fill d u (Box dir i d') vs) f | (f `ap` i) `direq` mirror dir =
  res (head vs) (f `minus` i)
res (Fill d u (Box dir i d') vs) f | isJust cand =
  res v (f `minus` j)
  where cand = findIndex (\j -> j `elem` ndef f) d'
        n = fromJust cand
        j = d' !! n
        -- TODO: This will be nicer with a better box input type
        v = vs !! (1+ 2*n + if (f `ap` j) `direq` True then 1 else 0)
res (Fill d u (Box dir i d') vs) f | (f `ap` i) `direq` dir =
  res (com d u (Box dir i d') vs) (f `minus` i) -- This will be a Com
res (Fill d u (Box dir i d') vs) f | (i:d') `subset` def f = -- otherwise?
  fill (cod f) (res u f)
       (Box dir (f `dap` i) (map (f `dap`) d'))
       (resBox i d' vs f)
res (Fill d u (Box dir i d') vs) f = error "Fill: not possible?"
res (Com d u (Box dir i d') vs) f = -- here: i:dom f = d
  res (res (fill d u (Box dir i d') vs) g) ytodir
  where x = gensym d
        co = cod f
        y = gensym co
        itox = update (identity (dom f)) [i] [x] -- (i=x):d->(d-i),x
        fxtoy = update f [x] [y] -- (f,x=y):(d-i),x -> co,y
        ytodir = face (y:co) y dir   -- (y=dir):co,y -> co
        -- note that: (i=dir) f = (i=x) (f,x=y) (y=dir)
        g = itox `comp` fxtoy   -- defined on x, hence non-circular call to res
-- res v f = Res v f
--res _ _ = error "res: not possible?"

modBox :: Name -> Dim -> [Val] -> (Name -> Mor) -> [Val]
modBox i d vs f = zipWith (\j v -> res v (f j)) idd vs
  where idd = i : concatMap (\j -> [j,j]) d

-- (box i d vs) f
-- i  = what we fill along
-- d  = dimension
-- vs = open box
resBox :: Name -> Dim -> [Val] -> Mor -> [Val]
resBox i d vs f = modBox i d vs (\j -> f `minus` j)

subset :: Eq a => [a] -> [a] -> Bool
subset xs ys = all (`elem` ys) xs

rec :: Dim -> Val -> Val -> Val -> Val
rec _ vz _ VZ = vz
rec d vz vs (VS v) = app d (app d vs v) (rec d vz vs v)
rec _ vz vs ne = VRec vz vs ne

----

ex1 = Rec Z (Lam (Lam (S $ Var 0))) (S (S (S Z)))

