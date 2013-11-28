module Eval where

import Data.List
import Data.Either
import Data.Maybe

import Debug.Trace

import Core

type Name = Integer
type Dim  = [Name]
type Dir  = Bool
-- True = Up; False = Down

dimeq :: Dim -> Dim -> Bool
dimeq d d' = sort (nub d) == sort (nub d')

gensym :: Dim -> Name
gensym [] = 0
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
ndef (al, _)  = [ i | (i, Left _) <- al ]

-- update f x y is (f, x=y) (x and y fresh)
update :: Mor -> Name -> Name -> Mor
update (al,co) x y = ((x,Right y):al, y:co)

im :: Mor -> Dim
im (al, _) = [ y | (_, Right y) <- al ]

ap :: Mor -> Name -> Either Dir Name
f@(al, _) `ap` i = case lookup i al of
  Just x    -> x
  otherwise -> error $ "ap: " ++ show f ++ " undefined on " ++ show i

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
-- deg d c | d /= nub d = error $ "deg " ++ show d ++ " and " ++ show c
--         | otherwise  = (map (\i -> (i, Right i)) d, c)
deg d _ = identity d

-- Compute the face map.
-- (i=b) : d -> d-i
face :: Dim -> Name -> Dir -> Mor
face d i b = ((i, Left b):[(j, Right j) | j <- di], di)
  where di | i `elem` d = delete i d
           | otherwise  = error $ "face " ++ show i ++ " not in " ++ show d

-- If f : I->J and f defined on i, then (f-i): I-i -> J-fi
-- If f : I->J and f not defined on i, then (f-i): I-i -> J
minus :: Mor -> Name -> Mor
(f@(al,co)) `minus` i = ([(j,v)| (j,v) <- al, i/=j] , co')
  where co' | i `elem` def f = delete (f `dap` i) co
            | otherwise = co

-- TODO: rename into BoxShape ?
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
boxSide (BoxContent _ vs) n False = fst $ vs !! n
boxSide (BoxContent _ vs) n True  = snd $ vs !! n

-- assumes the list is of odd size
toBox :: [Val] -> BoxContent
toBox (v:vs) = BoxContent v (pairing vs)
  where pairing [] = []
        pairing (v1:v2:vs) = (v1,v2):pairing vs
        pairing _ = error "toBox: wrong box format (not odd)"
toBox _ = error "toBox: wrong box format (empty box)"

fromBox :: BoxContent -> [Val]
fromBox (BoxContent v vs) = v:foldr (\(v1, v2) ws -> v1:v2:ws) [] vs

-- mapBox :: (Val -> Val) -> (BoxContent -> BoxContent)
-- mapBox f (BoxContent v vs) = BoxContent (f v) [(f v, f w) | (v, w) <- vs]

mapBox :: (Val -> Val) -> BoxContent -> BoxContent
mapBox f = toBox . map f . fromBox


mirror :: Dir -> Dir
mirror = not

direq :: Either Dir Name -> Dir -> Bool
Left False `direq` False = True
Left True `direq` True = True
_ `direq` _ = False

data KanType = Fill | Com
  deriving (Show, Eq)

data Val = VU
         | Ter Ter Env
         | VId Val Val Val
         | Path Val             -- tag values which are paths
         | VExt Name Dim Val Val Val Val -- has dimension (name:dim);
                                         -- vals of dimension dim
         | VPi Val Val
         | VApp Val Val         -- not needed for closed terms
         | VInh Val
         | VInc Val
         | VSquash Name Dim Val Val  -- has dimension (name:dim); vals
                                     -- of dimension dim
         | VCon Ident [Val]
         | Kan KanType Dim Val BoxShape BoxContent
         | VLSum [(Ident,[Val])]
--         | VInhRec Dim Val Val Val Val -- not needed for closed terms

--         | Res Val Mor              -- not needed for closed terms

--         | VBranch [(Ident,Ter)] Env
--         | VBranch [(Ident,Val)]
--         | VTrans Val Val Val   -- ?? needed
  deriving (Show, Eq)

data Env = Empty
         | Pair Env Val
         | PDef [Ter] Env
  deriving (Eq,Show)

upds :: Env -> [Val] -> Env
upds = foldl Pair

look :: Int -> Dim -> Env -> Val
look 0 d (Pair _ u)     = u
look k d (Pair s _)     = look (k-1) d s
look k d r@(PDef es r1) = look k d (upds r1 (evals d r es))

ter :: Dim -> Val -> Val
ter d (Ter t e) = eval d e t

evals :: Dim -> Env -> [Ter] -> [Val]
evals d e = map (eval d e)

mapEnv :: (Val -> Val) -> Env -> Env
mapEnv _ Empty = Empty
mapEnv f (Pair e v) = Pair (mapEnv f e) (f v)
mapEnv f (PDef ts e) = PDef ts (mapEnv f e)

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
        box = BoxShape True x []
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
              (BoxShape True x [y]) (BoxContent uy [(ux,pv)]) -- y:x:d
      thetaxtoz = theta `res` update (identity dy) x z        -- z:y:d
      sigma = Path thetaxtoz                              -- y:d
      omega = theta `res` face dxy x True                 -- y:d
      cv = eval dy ey c                                   -- y:d
      shape = BoxShape True y []
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
            (BoxShape True x [y]) (BoxContent uy [(ux,ux)])
    thetaxtoz = theta `res` update (identity dy) x z
    sigma = Path thetaxtoz
    omega = theta `res` face dxy x True
    cv = eval dy ey c
    shape = BoxShape True y []
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


inhrec :: Dim -> Val -> Val -> Val -> Val -> Val
inhrec d _ _ phi (VInc a) = app d phi a
inhrec d' b p phi (VSquash x d a0 a1) = -- dim. of b,p,phi is x:d
  app d (app d p b0) b1                 -- d' should be x:d
  where fc w dir = res w (face (x:d) x dir)
        b0 = inhrec d (fc b False) (fc p False) (fc phi False) a0
        b1 = inhrec d (fc b True) (fc p True) (fc phi True) a1
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
        ax  = res a (deg d (x:d)) -- dim x:d
        BoxContent vx vsx = modBox True i d' bc
                    (\_ j v -> let dj = delete j d
                                   f  = update (identity dj) (gensym dj) x
                             in res (unPath v) f)
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
fill d v b vs = Kan Fill d v b vs

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
--  trace ("Pi fill\n")
  com (x:d) (app (x:d) bx vfill) (BoxShape True x (i:d')) wvfills
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
        wuis = if dir then (wuidir,wuimdir) else (wuimdir,wuidir)
        -- final open box in (app bx vsfill)
        wvfills = BoxContent wux0 (wuis:wbox')
app d (VExt x d' bv fv gv pv) w = -- d = x:d'; values in vext have dim d'
  com (y:d) (app (y:d) bvxy wy) (BoxShape True y [x]) (BoxContent pvxw [(left,right)])
  -- NB: there are various choices how to construct this
  where y = gensym d
        bvxy = res bv (deg d' (y:d))
        wy = res w (deg d (y:d))
        w0 = res w (face d x False)
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
res (VExt x d bv fv gv pv) f | (f `ap` x) `direq` False = fv `res` (f `minus` x)
res (VExt x d bv fv gv pv) f | (f `ap` x) `direq` True = gv `res` (f `minus` x)
res (VInh v) f = VInh (res v f)
res (VInc v) f = VInc (res v f)
res (VSquash x d u v) f | x `elem` def f = -- dom f = x:d
  VSquash (f `dap` x) d' (res u fminusx) (res v fminusx)
  where -- f-x : d -> d' ; f : x:d -> cod f;
        fminusx = f `minus` x
        d' = cod fminusx
res (VSquash x d u v) f | x `elem` dom f && (f `ap` x) `direq` False = res u (f `minus` x)
res (VSquash x d u v) f | x `elem` dom f && (f `ap` x) `direq` True = res v (f `minus` x)
res (VSquash x d u v) f = error $ "Vsquash impossible d= " ++ show d ++ " f = " ++ show f
--res (VInhRec b p phi a) f = inhrec (res b f) (res p f) (res phi f) (res a f)
--res (VBranch alts) f = VBranch $ map (\(n,v) -> (n,  res v f)) alts
res (VCon name vs) f = VCon name (map (`res` f) vs)
--res (VLSum nass) f = VLSum $ map (\(n,as) -> (n, map (`res` f) as)) nass

-- res v f = Res v f
--res _ _ = error "res: not possible?"

-- Takes a u and returns an open box u's given by the specified faces.
cubeToBox :: Val -> Dim -> BoxShape -> BoxContent
cubeToBox u d (BoxShape dir i d') =
  BoxContent (get i dir) [ (get j False, get j True) | j <- d']
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
  BoxContent (f dir i v) (zipWith (\j (v, w) -> (f False j v, f True j w)) d vs)

-- (box i d vs) f
-- i  = what we fill along
-- d  = dimension
-- vs = open box
resBox :: Name -> Dim -> BoxContent -> Mor -> BoxContent
resBox i d bc f = modBox True i d bc (\_ j v -> res v (f `minus` j))

-- assumes f is defined on i:d'
resShape :: BoxShape -> Mor -> BoxShape
resShape (BoxShape dir i d') f =
  BoxShape dir (f `dap` i) (map (f `dap`) d')

subset :: Eq a => [a] -> [a] -> Bool
subset xs ys = all (`elem` ys) xs
