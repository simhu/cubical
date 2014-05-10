{-# LANGUAGE TupleSections #-}
module CTT where

import Control.Applicative
import Data.List
import Data.Maybe
import Pretty

--------------------------------------------------------------------------------
-- | Terms

data Loc = Loc { locFile :: String
               , locPos :: (Int, Int) }
  deriving Eq

type Ident  = String
type Label  = String
type Binder = (Ident,Loc)

noLoc :: String -> Binder
noLoc x = (x, Loc "" (0,0))

-- Branch of the form: c x1 .. xn -> e
type Brc    = (Label,([Binder],Ter))

-- Telescope (x1 : A1) .. (xn : An)
type Tele   = [(Binder,Ter)]

-- Labelled sum: c (x1 : A1) .. (xn : An)
type LblSum = [(Binder,Tele)]

-- Context gives type values to identifiers
type Ctxt   = [(Binder,Val)]

-- Mutual recursive definitions: (x1 : A1) .. (xn : An) and x1 = e1 .. xn = en
type Decls  = [(Binder,Ter,Ter)]
data ODecls = ODecls Decls
            | Opaque Binder
            | Transp Binder
  deriving (Eq,Show)

declIdents :: Decls -> [Ident]
declIdents decl = [ x | ((x,_),_,_) <- decl]

declBinders :: Decls -> [Binder]
declBinders decl = [ x | (x,_,_) <- decl]

declTers :: Decls -> [Ter]
declTers decl = [ d | (_,_,d) <- decl]

declTele :: Decls -> Tele
declTele decl = [ (x,t) | (x,t,_) <- decl]

declDefs :: Decls -> [(Binder,Ter)]
declDefs decl = [ (x,d) | (x,_,d) <- decl]

-- Terms
data Ter = App Ter Ter
         | Pi Ter Ter
         | Lam Binder Ter
         | Sigma Ter Ter
         | SPair Ter Ter
         | Fst Ter
         | Snd Ter
         | Where Ter ODecls
         | Var Ident
         | U
         -- constructor c Ms
         | Con Label [Ter]
         -- branches c1 xs1  -> M1,..., cn xsn -> Mn
         | Split Loc [Brc]
         -- labelled sum c1 A1s,..., cn Ans (assumes terms are constructors)
         | Sum Binder LblSum
         | PN PN
  deriving Eq

-- Primitive notions
data PN = Id | Refl
        -- Inh A is an h-prop stating that A is inhabited.
        -- Here we take h-prop A as (Pi x y : A) Id A x y.
        | Inh
        -- Inc a : Inh A for a:A (A not needed ??)
        | Inc
        -- Squash a b : Id (Inh A) a b
        | Squash
        -- InhRec B p phi a : B,
        -- p : hprop(B), phi : A -> B, a : Inh A (cf. HoTT-book p.113)
        | InhRec

        -- (A B : U) -> Id U A B -> A -> B
        -- For TransU we only need the eqproof and the element in A is needed
        | TransU

        -- (A B : U) -> Id U A B -> B -> A
        -- For TransU we only need the eqproof and the element in A is needed
        | TransInvU

        -- (A : U) -> (a : A) -> Id A a (transport A (refl U A) a)
        | TransURef

        -- (A : U) (a b:A) (p:Id A a b) -> Id (singl A a) (pair a (refl A a)) (pair b p)
        | CSingl

        -- (A B : U) (f : A -> B) (a b : A) ->
        -- (p : Id A a b) -> Id B (f a) (f b)
        -- TODO: remove?
        | MapOnPath

        -- (A B : U) (f g : A -> B) (a b : A) ->  
        -- Id (A->B) f g -> Id A a b -> Id B (f a) (g b)
        | AppOnPath

        -- Ext B f g p : Id (Pi A B) f g,
        -- (p : (Pi x:A) Id (Bx) (fx,gx)); A not needed ??
        -- | Ext

        -- Ext B f g p : Id (Pi A B) f g,
        -- (p : (Pi x y:A) IdS A (Bx) x y p fx gy)
        | HExt

        -- EquivEq A B f s t where
        -- A, B are types, f : A -> B,
        -- s : (y : B) -> fiber f y, and
        -- t : (y : B) (z : fiber f y) -> Id (fiber f y) (s y) z
        -- where fiber f y is Sigma x : A. Id B (f x) z.
        | EquivEq
        -- (A : U) -> (s : (y : A) -> pathTo A a) ->
        -- (t : (y : B) -> (v : pathTo A a) -> Id (path To A a) (s y) v) ->
        -- Id (Id U A A) (refl U A) (equivEq A A (id A) s t)
        | EquivEqRef

        -- (A B : U) -> (f : A -> B) (s : (y : B) -> fiber A B f y) ->
        -- (t : (y : B) -> (v : fiber A B f y) -> Id (fiber A B f y) (s y) v) ->
        -- (a : A) -> Id B (f a) (transport A B (equivEq A B f s t) a)
        | TransUEquivEq

        -- IdP  :    (A B :U) -> Id U A B ->  A -> B -> U
        -- IdP A B p a b   is the type of paths  connecting a to b over p
        | IdP

        -- mapOnPathD :  (A : U) (F : A -> U) (f : (x : A) -> F x) (a0 a1 : A) (p : Id A a0 a1) ->
        --               IdS A F a0 a1 p  (f a0) (f a1)
        -- IdS : (A:U) (F:A -> U) (a0 a1:A) (p:Id A a0 a1) -> F a0 -> F a1 -> U
        -- IdS A F a0 a1 p = IdP (F a0) (F a1) (mapOnPath A U F a0 a1 p)
        -- TODO: remove in favor of AppOnPathD?
        | MapOnPathD

        -- AppOnPathD :  (A : U) (F : A -> U) (f g : (x : A) -> F x) -> Id ((x : A) -> F x) f g ->
        --               (a0 a1 : A) (p : Id A a0 a1) -> IdS A F a0 a1 p  (f a0) (g a1)
        -- | AppOnPathD

        -- mapOnPathS : (A:U)(F:A -> U) (C:U) (f: (x:A) -> F x -> C) (a0 a1 : A) (p:Id A a0 a1)
        -- (b0:F a0) (b1:F a1) (q : IdS A F a0 a1 p b0 b1) -> Id C (f a0 b0) (f a1 b1)
        | MapOnPathS -- TODO: AppOnPathS?

        -- S1 : U
        | Circle

        -- base : S1
        | Base

        -- loop : Id S1 base base
        | Loop

        -- S1rec : (F : S1 -> U) (b : F base) (l : IdS F base base loop) (x : S1) -> F x
        | CircleRec

        -- I : U
        | I

        -- I0, I1 : Int
        | I0 | I1

        -- line : Id Int I0 I1
        | Line


        -- intrec : (F : I -> U) (s : F I0) (e : F I1)
        --  (l : IdS Int F I0 I1 line s e) (x : I) -> F x
        | IntRec

        -- undefined constant
        | Undef Loc
  deriving (Eq, Show)

-- For an expression t, returns (u,ts) where u is no application
-- and t = u t
unApps :: Ter -> (Ter,[Ter])
unApps = aux []
  where aux :: [Ter] -> Ter -> (Ter,[Ter])
        aux acc (App r s) = aux (s:acc) r
        aux acc t         = (t,acc)
-- Non tail reccursive version:
-- unApps (App r s) = let (t,ts) = unApps r in (t, ts ++ [s])
-- unApps t         = (t,[])

mkApps :: Ter -> [Ter] -> Ter
mkApps (Con l us) vs = Con l (us ++ vs)
mkApps t ts          = foldl App t ts

mkLams :: [String] -> Ter -> Ter
mkLams bs t = foldr Lam t [noLoc b | b <- bs]

mkWheres :: [ODecls] -> Ter -> Ter
mkWheres []     e = e
mkWheres (d:ds) e = Where (mkWheres ds e) d

-- Primitive notions
primHandle :: [(Ident,Int,PN)]
primHandle =
  [("Id"            , 3,  Id           ),
   ("refl"          , 2,  Refl         ),
   -- ("funExt"        , 5,  Ext          ),
   ("funHExt"       , 5,  HExt          ),
   ("inh"           , 1,  Inh          ),
   ("inc"           , 2,  Inc          ),
   ("squash"        , 3,  Squash       ),
   ("inhrec"        , 5,  InhRec       ),
   ("equivEq"       , 5,  EquivEq      ),
   ("transport"     , 4,  TransU       ),
   ("transpInv"     , 4,  TransInvU    ),
   ("contrSingl"    , 4,  CSingl       ),
   ("transportRef"  , 2,  TransURef    ),
   ("equivEqRef"    , 3,  EquivEqRef   ),
   ("transpEquivEq" , 6,  TransUEquivEq),
   ("appOnPath"     , 8,  AppOnPath    ),
   ("mapOnPath"     , 6,  MapOnPath    ),
   ("IdP"           , 5,  IdP          ),
   ("mapOnPathD"    , 6,  MapOnPathD   ),
   ("mapOnPathS"    , 10, MapOnPathS   ),
   ("S1"            , 0,  Circle       ),
   ("base"          , 0,  Base         ),
   ("loop"          , 0,  Loop         ),
   ("S1rec"         , 4,  CircleRec    ),
   ("I"             , 0,  I            ),
   ("I0"            , 0,  I0           ),
   ("I1"            , 0,  I1           ),
   ("line"          , 0,  Line         ),
   ("intrec"        , 5,  IntRec       )]

reservedNames :: [String]
reservedNames = [ s | (s,_,_) <- primHandle ]

arity :: PN -> Int
arity pn = fromMaybe 0 $ listToMaybe [n | (_,n,pn') <- primHandle, pn == pn']

mkPN :: String -> Maybe PN
mkPN s = listToMaybe [pn | (s',_,pn) <- primHandle, s == s']

--------------------------------------------------------------------------------
-- | Names, dimension, and nominal type class

type Name = Integer
type Dim  = [Name]

gensym :: Dim -> Name
gensym [] = 2
gensym xs = maximum xs + 1

gensyms :: Dim -> [Name]
gensyms d = let x = gensym d in x : gensyms (x : d)

class Nominal a where
  swap :: a -> Name -> Name -> a
  support :: a -> [Name]

fresh :: Nominal a => a -> Name
fresh = gensym . support

freshs :: Nominal a => a -> [Name]
freshs = gensyms . support

instance (Nominal a, Nominal b) => Nominal (a, b) where
  support (a, b)  = support a `union` support b
  swap (a, b) x y = (swap a x y, swap b x y)

instance Nominal a => Nominal [a]  where
  support vs  = unions (map support vs)
  swap vs x y = [swap v x y | v <- vs]

-- Make Name an instance of Nominal
instance Nominal Integer where
  support 0 = []
  support 1 = []
  support n = [n]

  swap z x y | z == x    = y
             | z == y    = x
             | otherwise = z

--------------------------------------------------------------------------------
-- | Boxes

-- TODO: abstract the type of Intervals instead of exposing the encoding
type Dir = Integer

mirror :: Dir -> Dir
mirror 0 = 1
mirror 1 = 0
mirror n = error $ "mirror: 0 or 1 expected but " ++ show n ++ " given"

up, down :: Dir
up   = 1
down = 0

type Side = (Name,Dir)

allDirs :: [Name] -> [Side]
allDirs []     = []
allDirs (n:ns) = (n,down) : (n,up) : allDirs ns

data Box a = Box { dir   :: Dir
                 , pname :: Name
                 , pface :: a
                 , sides :: [(Side,a)] }
  deriving Eq

instance Show a => Show (Box a) where
  show (Box dir n f xs) = "Box" <+> show dir <+> show n <+> show f <+> show xs

mapBox :: (a -> b) -> Box a -> Box b
mapBox f (Box d n x xs) = Box d n (f x) [ (nnd,f v) | (nnd,v) <- xs ]

sequenceSnd :: Monad m => [(a,m b)] -> m [(a,b)]
sequenceSnd []          = return []
sequenceSnd ((a,b):abs) = do
  b' <- b
  acs <- sequenceSnd abs
  return $ (a,b') : acs

sequenceBox :: Monad m => Box (m a) -> m (Box a)
sequenceBox (Box d n x xs) = do
  x' <- x
  xs' <- sequenceSnd xs
  return $ Box d n x' xs'

mapBoxM :: Monad m => (a -> m b) -> Box a -> m (Box b)
mapBoxM f = sequenceBox . mapBox f

instance Functor Box where
  fmap = mapBox

lookBox :: Show a => Side -> Box a -> a
lookBox (y,dir) (Box d x v _)  | x == y && mirror d == dir = v
lookBox xd box@(Box _ _ _ nvs) = case lookup xd nvs of
  Just v  -> v
  Nothing -> error $ "lookBox: box not defined on " ++
                      show xd ++ "\nbox = " ++ show box

nonPrincipal :: Box a -> [Name]
nonPrincipal (Box _ _ _ nvs) = nub $ map (fst . fst) nvs

defBox :: Box a -> [(Name, Dir)]
defBox (Box d x _ nvs) = (x,mirror d) : [ zd | (zd,_) <- nvs ]

fromBox :: Box a -> [(Side,a)]
fromBox (Box d x v nvs) = ((x, mirror d),v) : nvs

modBox :: (Side -> a -> b) -> Box a -> Box b
modBox f (Box dir x v nvs) =
  Box dir x (f (x,mirror dir) v) [ (nd,f nd v) | (nd,v) <- nvs ]

modBoxM :: Monad m => (Side -> a -> m b) -> Box a -> m (Box b)
modBoxM f = sequenceBox . modBox f

-- Restricts the non-principal faces to np.
subBox :: [Name] -> Box a -> Box a
subBox np (Box dir x v nvs) =
  Box dir x v [ nv | nv@((n,_),_) <- nvs, n `elem` np]

shapeOfBox :: Box a -> Box ()
shapeOfBox = mapBox (const ())

-- fst is down, snd is up
consBox :: (Name,(a,a)) -> Box a -> Box a
consBox (n,(v0,v1)) (Box dir x v nvs) =
  Box dir x v $ ((n,down),v0) : ((n,up),v1) : nvs

appendBox :: [(Name,(a,a))] -> Box a -> Box a
appendBox xs b = foldr consBox b xs

appendSides :: [(Side, a)] -> Box a -> Box a
appendSides sides (Box dir x v nvs) = Box dir x v (sides ++ nvs)

transposeBox :: Box [a] -> [Box a]
transposeBox b@(Box dir _ [] _)      = []
transposeBox (Box dir x (v:vs) nvss) =
  Box dir x v [ (nnd,head vs) | (nnd,vs) <- nvss ] :
  transposeBox (Box dir x vs [ (nnd,tail vs) | (nnd,vs) <- nvss ])

-- Nominal for boxes
instance Nominal a => Nominal (Box a) where
  support (Box dir n v nvs)  = support ((n, v), nvs)
  swap (Box dir z v nvs) x y = Box dir z' v' nvs' where
    ((z',v'), nvs') = swap ((z, v), nvs) x y

--------------------------------------------------------------------------------
-- | Values

data KanType = Fill | Com
  deriving (Show, Eq)

data Val = VU
         | Ter Ter OEnv
         | VPi Val Val
         | VId Val Val Val

         | VSigma Val Val
         | VSPair Val Val

         -- tag values which are paths
         | Path Name Val

         -- | VExt Name Val Val Val Val
         | VHExt Name Val Val Val Val

         -- inhabited
         | VInh Val

         -- inclusion into inhabited
         | VInc Val

         -- squash type - connects the two values along the name
         | VSquash Name Val Val

         | VCon Ident [Val]

         | Kan KanType Val (Box Val)

         -- of type U connecting a and b along x
         -- VEquivEq x a b f s t
         | VEquivEq Name Val Val Val Val Val

         -- names x, y and values a, s, t
         | VEquivSquare Name Name Val Val Val

         -- of type VEquivEq
         | VPair Name Val Val

         -- of type VEquivSquare
         | VSquare Name Name Val

         -- a value of type Kan Com VU (Box (type of values))
         | VComp (Box Val)

         -- a value of type Kan Fill VU (Box (type of values minus name))
         -- the name is bound
         | VFill Name (Box Val)

         -- circle
         | VCircle
         | VBase
         | VLoop Name -- has type VCircle and connects base along the name

         -- interval
         | VI
         | VI0
         | VI1
         | VLine Name           -- connects start and end point along name

         -- neutral values
         | VApp Val Val            -- the first Val must be neutral
         | VAppName Val Name
         | VSplit Val Val          -- the second Val must be neutral
         | VVar String Dim
         | VInhRec Val Val Val Val     -- the last Val must be neutral
         | VCircleRec Val Val Val Val  -- the last Val must be neutral
         | VIntRec Val Val Val Val Val -- the last Val must be neutral
         | VFillN Val (Box Val)
         | VComN Val (Box Val)
         | VFst Val
         | VSnd Val
  deriving Eq

vepair :: Name -> Val -> Val -> Val
vepair x a b = VSPair a (Path x b)

mkVar :: Int -> Dim -> Val
mkVar k = VVar ('X' : show k)

isNeutral :: Val -> Bool
isNeutral (VApp u _)           = isNeutral u
isNeutral (VAppName u _)       = isNeutral u
isNeutral (VSplit _ v)         = isNeutral v
isNeutral (VVar _ _)           = True
isNeutral (VInhRec _ _ _ v)    = isNeutral v
isNeutral (VCircleRec _ _ _ v) = isNeutral v
isNeutral (VIntRec _ _ _ _ v)  = isNeutral v
isNeutral (VFillN _ _)         = True
isNeutral (VComN _ _)          = True
isNeutral (VFst v)             = isNeutral v
isNeutral (VSnd v)             = isNeutral v
isNeutral _                    = False

fstVal, sndVal, unSquare :: Val -> Val
fstVal (VPair _ a _)     = a
fstVal x                 = error $ "error fstVal: " ++ show x
sndVal (VPair _ _ v)     = v
sndVal x                 = error $ "error sndVal: " ++ show x
unSquare (VSquare _ _ v) = v
unSquare v               = error $ "unSquare bad input: " ++ show v

unCon :: Val -> [Val]
unCon (VCon _ vs) = vs
unCon v           = error $ "unCon: not a constructor: " ++ show v

unions :: Eq a => [[a]] -> [a]
unions = foldr union []

unionsMap :: Eq b => (a -> [b]) -> [a] -> [b]
unionsMap f = unions . map f

instance Nominal Val where
  support VU                            = []
  support (Ter _ e)                     = support e
  support (VId a v0 v1)                 = support [a,v0,v1]
  support (Path x v)                    = delete x $ support v
  support (VInh v)                      = support v
  support (VInc v)                      = support v
  support (VPi v1 v2)                   = support [v1,v2]
  support (VCon _ vs)                   = support vs
  support (VSquash x v0 v1)             = support (x, [v0,v1])
  -- support (VExt x b f g p)           = support (x, [b,f,g,p])
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
  support (VApp u v)                    = support (u, v)
  support (VAppName u n)                = support (u, n)
  support (VSplit u v)                  = support (u, v)
  support (VVar x d)                    = support d
  support (VSigma u v)                  = support (u,v)
  support (VSPair u v)                  = support (u,v)
  support (VFst u)                      = support u
  support (VSnd u)                      = support u
  support (VInhRec b p h a)             = support [b,p,h,a]
  support VCircle                       = []
  support VBase                         = []
  support (VLoop n)                     = [n]
  support (VCircleRec f b l s)          = support [f,b,l,s]
  support VI                            = []
  support VI0                           = []
  support VI1                           = []
  support (VLine n)                     = [n]
  support (VIntRec f s e l u)           = support [f,s,e,l,u]
  support v                             = error ("support " ++ show v)

  swap u x y =
    let sw u = swap u x y in case u of
    VU                     -> VU
    Ter t e                -> Ter t (sw e)
    VId a v0 v1            -> VId (sw a) (sw v0) (sw v1)
    Path z v               -> Path (sw z) (sw v)
    -- VExt z b f g p      -> VExt (swap z x y) (sw b) (sw f) (sw g) (sw p)
    VHExt z b f g p        -> VHExt (sw z) (sw b) (sw f) (sw g) (sw p)
    VPi a f                -> VPi (sw a) (sw f)
    VInh v                 -> VInh (sw v)
    VInc v                 -> VInc (sw v)
    VSquash z v0 v1        -> VSquash (sw z) (sw v0) (sw v1)
    VCon c us              -> VCon c (map sw us)
    VEquivEq z a b f s t   ->
      VEquivEq (sw z) (sw a) (sw b) (sw f) (sw s) (sw t)
    VPair z a v            -> VPair (sw z) (sw a) (sw v)
    VEquivSquare z w a s t ->
      VEquivSquare (sw z) (sw w) (sw a) (sw s) (sw t)
    VSquare z w v          -> VSquare (sw z) (sw w) (sw v)
    Kan Fill a b           -> Kan Fill (sw a) (sw b)
    VFillN a b             -> VFillN (sw a) (sw b)
    Kan Com a b            -> Kan Com (sw a) (sw b)
    VComN a b              -> VComN (sw a) (sw b)
    VComp b                -> VComp (sw b)
    VFill z b              -> VFill (sw z) (sw b)
    VApp u v               -> VApp (sw u) (sw v)
    VAppName u n           -> VAppName (sw u) (sw n)
    VSplit u v             -> VSplit (sw u) (sw v)
    VVar s d               -> VVar s (sw d)
    VSigma u v             -> VSigma (sw u) (sw v)
    VSPair u v             -> VSPair (sw u) (sw v)
    VFst u                 -> VFst (sw u)
    VSnd u                 -> VSnd (sw u)
    VInhRec b p h a        -> VInhRec (sw b) (sw p) (sw h) (sw a)
    VCircle                -> VCircle
    VBase                  -> VBase
    VLoop z                -> VLoop (sw z)
    VCircleRec f b l a     -> VCircleRec (sw f) (sw b) (sw l) (sw a)
    VI                     -> VI
    VI0                    -> VI0
    VI1                    -> VI1
    VLine z                -> VLine (sw z)
    VIntRec f s e l u      -> VIntRec (sw f) (sw s) (sw e) (sw l) (sw u)


--------------------------------------------------------------------------------
-- | Environments

data Env = Empty
         | Pair Env (Binder,Val)
         | PDef [(Binder,Ter)] Env
  deriving Eq

instance Show Env where
  show Empty            = ""
  show (PDef xas env)   = show env
  show (Pair env (x,u)) = parens $ showEnv1 env ++ show u
    where
      showEnv1 (Pair env (x,u)) = showEnv1 env ++ show u ++ ", "
      showEnv1 e                = show e

instance Nominal Env where
  swap e x y = mapEnv (\u -> swap u x y) e

  support Empty          = []
  support (Pair e (_,v)) = support (e, v)
  support (PDef _ e)     = support e

data OEnv = OEnv { env     :: Env,
                   opaques :: [Binder] }
  deriving Eq

oEmpty :: OEnv
oEmpty = OEnv Empty []

oPair :: OEnv -> (Binder,Val) -> OEnv
oPair (OEnv e o) u = OEnv (Pair e u) o

oPDef :: Bool -> ODecls -> OEnv -> OEnv
oPDef _    (ODecls decls)  (OEnv e o) = OEnv (PDef [(x,d) | (x,_,d) <- decls] e) o
oPDef True (Opaque d)      (OEnv e o) = OEnv e (d:o)
oPDef True (Transp d)      (OEnv e o) = OEnv e (d `delete` o)
oPDef _ _ e = e

instance Show OEnv where
  show (OEnv e s) = show e -- <+> parens ("with opaque:" <+> ccat s)

instance Nominal OEnv where
  swap (OEnv e s) x y = OEnv (swap e x y) s
  support (OEnv e s)  = support e

upds :: OEnv -> [(Binder,Val)] -> OEnv
upds = foldl oPair

lookupIdent :: Ident -> [(Binder,a)] -> Maybe (Binder, a)
lookupIdent x defs = lookup x [(y,((y,l),t)) | ((y,l),t) <- defs]

getIdent :: Ident -> [(Binder,a)] -> Maybe a
getIdent x defs = do (_,t) <- lookupIdent x defs; return t

getBinder :: Ident -> [(Binder,a)] -> Maybe Binder
getBinder x defs = do (b,_) <- lookupIdent x defs; return b

mapEnv :: (Val -> Val) -> Env -> Env
mapEnv _ Empty          = Empty
mapEnv f (Pair e (x,v)) = Pair (mapEnv f e) (x,f v)
mapEnv f (PDef ts e)    = PDef ts (mapEnv f e)

mapEnvM :: Applicative m => (Val -> m Val) -> Env -> m Env
mapEnvM _ Empty          = pure Empty
mapEnvM f (Pair e (x,v)) = Pair <$> mapEnvM f e <*> ( (x,) <$> f v)
mapEnvM f (PDef ts e)    = PDef ts <$> mapEnvM f e

mapOEnv :: (Val -> Val) -> OEnv -> OEnv
mapOEnv f (OEnv e o) = OEnv (mapEnv f e) o

mapOEnvM :: Applicative m => (Val -> m Val) -> OEnv -> m OEnv
mapOEnvM f (OEnv e o) = flip OEnv o <$> mapEnvM f e

valOfEnv :: Env -> [Val]
valOfEnv Empty            = []
valOfEnv (Pair env (_,v)) = v : valOfEnv env
valOfEnv (PDef _ env)     = valOfEnv env

valOfOEnv :: OEnv -> [Val]
valOfOEnv (OEnv e o) = valOfEnv e

--------------------------------------------------------------------------------
-- | Pretty printing

instance Show Loc where
  show (Loc name (i,j)) = name ++ "_L" ++ show i ++ "_C" ++ show j

instance Show Ter where
  show = showTer

showTer :: Ter -> String
showTer U                 = "U"
showTer (App e0 e1)       = showTer e0 <+> showTer1 e1
showTer (Pi e0 e1)        = "Pi" <+> showTers [e0,e1]
showTer (Lam (x,_) e)         = '\\' : x <+> "->" <+> showTer e
showTer (Fst e)           = showTer e ++ ".1"
showTer (Snd e)           = showTer e ++ ".2"
showTer (Sigma e0 e1)     = "Sigma" <+> showTers [e0,e1]
showTer (SPair e0 e1)      = "pair" <+> showTers [e0,e1]
showTer (Where e d)       = showTer e <+> "where" <+> showODecls d
showTer (Var x)           = x
showTer (Con c es)        = c <+> showTers es
showTer (Split l _)       = "split " ++ show l
showTer (Sum l _)         = "sum " ++ show l
showTer (PN pn)           = showPN pn

showTers :: [Ter] -> String
showTers = hcat . map showTer1

showTer1 :: Ter -> String
showTer1 U           = "U"
showTer1 (Con c [])  = c
showTer1 (Var x)     = x
showTer1 u@(Split{}) = showTer u
showTer1 u@(Sum{})   = showTer u
showTer1 u@(PN{})    = showTer u
showTer1 u           = parens $ showTer u

-- Warning: do not use showPN as a Show instance as it will loop
showPN :: PN -> String
showPN (Undef l) = show l
showPN pn              = case [s | (s,_,pn') <- primHandle, pn == pn'] of
  [s] -> s
  _   -> error $ "showPN: unknown primitive " ++ show pn

showDecls :: Decls -> String
showDecls defs = ccat (map (\((x,_),_,d) -> x <+> "=" <+> show d) defs)

showODecls :: ODecls -> String
showODecls (ODecls defs) = showDecls defs
showODecls (Opaque x)    = "opaque"      <+> show x
showODecls (Transp x)    = "transparent" <+> show x

instance Show Val where
  show = showVal

showVal :: Val -> String
showVal VU               = "U"
showVal (Ter t env)      = show t <+> show env
showVal (VId a u v)      = "Id" <+> showVal1 a <+> showVal1 u <+> showVal1 v
showVal (Path n u)       = abrack (show n) <+> showVal u
-- showVal (VExt n b f g p) = "funExt" <+> show n <+> showVals [b,f,g,p]
showVal (VHExt n b f g p) = "funHExt" <+> show n <+> showVals [b,f,g,p]
showVal (VCon c us)      = c <+> showVals us
showVal (VPi a f)        = "Pi" <+> showVals [a,f]
showVal (VInh u)         = "inh" <+> showVal1 u
showVal (VInc u)         = "inc" <+> showVal1 u
showVal (VInhRec b p h a) = "inhrec" <+> showVals [b,p,h,a]
showVal (VSquash n u v)  = "squash" <+> show n <+> showVals [u,v]
showVal (Kan Fill v box) = "Fill" <+> showVal1 v <+> parens (show box)
showVal (Kan Com v box)  = "Com" <+> showVal1 v <+> parens (show box)
showVal (VFillN v box)   = "FillN" <+> showVal1 v <+> parens (show box)
showVal (VComN v box)    = "ComN" <+> showVal1 v <+> parens (show box)
showVal (VPair n u v)    = "vpair" <+> show n <+> showVals [u,v]
showVal (VSquare x y u)  = "vsquare" <+> show x <+> show y <+> showVal1 u
showVal (VComp box)      = "vcomp" <+> parens (show box)
showVal (VFill n box)    = "vfill" <+> show n <+> parens (show box)
showVal (VApp u v)       = showVal u <+> showVal1 v
showVal (VAppName u n)   = showVal u <+> "@" <+> show n
showVal (VSplit u v)     = showVal u <+> showVal1 v
showVal (VVar x d)       = x <+> showDim d
showVal (VEquivEq n a b f _ _)   = "equivEq" <+> show n <+> showVals [a,b,f]
showVal (VEquivSquare x y a s t) =
  "equivSquare" <+> show x <+> show y <+> showVals [a,s,t]
showVal (VSPair u v)     = "pair" <+> showVals [u,v]
showVal (VSigma u v)     = "Sigma" <+> showVals [u,v]
showVal (VFst u)         = showVal u ++ ".1"
showVal (VSnd u)         = showVal u ++ ".2"
showVal VCircle          = "S1"
showVal VBase            = "base"
showVal (VLoop x)        = "loop" <+> show x
showVal (VCircleRec f b l s) = "S1rec" <+> showVals [f,b,l,s]
showVal VI               = "I"
showVal VI0              = "I0"
showVal VI1              = "I1"
showVal (VLine n)        = "line" <+> show n
showVal (VIntRec f s e l u) = "intrec" <+> showVals [f,s,e,l,u]

showDim :: Show a => [a] -> String
showDim = parens . ccat . map show

showVals :: [Val] -> String
showVals = hcat . map showVal1

showVal1 :: Val -> String
showVal1 VU           = "U"
showVal1 (VCon c [])  = c
showVal1 u@(VVar{})   = showVal u
showVal1 u            = parens $ showVal u

