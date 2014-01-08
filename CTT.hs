module CTT where


import Data.List
import Pretty

--------------------------------------------------------------------------------
-- | Terms

type Binder = String
type Def    = (Binder,Ter)  -- without type annotations for now
type Ident  = String
type Prim = (Integer,String)

data Ter = Var Binder
         | Id Ter Ter Ter | Refl Ter
         | Pi Ter Ter     | Lam Binder Ter | App Ter Ter
         | Where Ter [Def]
         | U

         | Undef Prim

           -- constructor c Ms
         | Con Ident [Ter]

           -- branches c1 xs1  -> M1,..., cn xsn -> Mn
         | Branch Prim [(Ident, ([Binder],Ter))]

           -- labelled sum c1 A1s,..., cn Ans (assumes terms are constructors)
         | LSum Prim [(Ident, [(Binder,Ter)])]

           -- (A B:U) -> Id U A B -> A -> B
           -- For TransU we only need the eqproof and the element in A is needed
         | TransU Ter Ter

           -- (A:U) -> (a : A) -> Id A a (transport A (refl U A) a)
           -- Argument is a
         | TransURef Ter

           -- The primitive J will have type:
           -- J : (A : U) (u : A) (C : (v : A) -> Id A u v -> U)
           --  (w : C u (refl A u)) (v : A) (p : Id A u v) -> C v p
         | J Ter Ter Ter Ter Ter Ter

           -- (A : U) (u : A) (C : (v:A) -> Id A u v -> U)
           -- (w : C u (refl A u)) ->
           -- Id (C u (refl A u)) w (J A u C w u (refl A u))
         | JEq Ter Ter Ter Ter

           -- Ext B f g p : Id (Pi A B) f g,
           -- (p : (Pi x:A) Id (Bx) (fx,gx)); A not needed ??
         | Ext Ter Ter Ter Ter

           -- Inh A is an h-prop stating that A is inhabited.
           -- Here we take h-prop A as (Pi x y : A) Id A x y.
         | Inh Ter

           -- Inc a : Inh A for a:A (A not needed ??)
         | Inc Ter

           -- Squash a b : Id (Inh A) a b
         | Squash Ter Ter

           -- InhRec B p phi a : B,
           -- p : hprop(B), phi : A -> B, a : Inh A (cf. HoTT-book p.113)
         | InhRec Ter Ter Ter Ter

           -- EquivEq A B f s t where
           -- A, B are types, f : A -> B,
           -- s : (y : B) -> fiber f y, and
           -- t : (y : B) (z : fiber f y) -> Id (fiber f y) (s y) z
           -- where fiber f y is Sigma x : A. Id B (f x) z.
         | EquivEq Ter Ter Ter Ter Ter

           -- (A : U) -> (s : (y : A) -> pathTo A a) ->
           -- (t : (y : B) -> (v : pathTo A a) -> Id (path To A a) (s y) v) ->
           -- Id (Id U A A) (refl U A) (equivEq A A (id A) s t)
         | EquivEqRef Ter Ter Ter

           -- (A B : U) -> (f : A -> B) (s : (y : B) -> fiber A B f y) ->
           -- (t : (y : B) -> (v : fiber A B f y) -> Id (fiber A B f y) (s y) v) ->
           -- (a : A) -> Id B (f a) (transport A B (equivEq A B f s t) a)
         | TransUEquivEq Ter Ter Ter Ter Ter Ter

           -- TODO: Remove, but first fix the bug that get introduced (it can
           -- be found by running testNO1 in nIso.cub)
         | Trans Ter Ter Ter
         | MapOnPath Ter Ter
           -- {A B : U} (f : A -> B) {a b : A} ->
           --  (p : Id A a b) -> Id B (f a) (f b)
  deriving Eq

instance Show Ter where
  show = showTer

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

type Dir = Integer

mirror :: Dir -> Dir
mirror 0 = 1
mirror 1 = 0
mirror n = error $ "mirror: 0 or 1 expected but " ++ show n ++ " given"

up, down :: Dir
up = 1
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

-- Showing boxes with parenthesis around
showBox :: Show a => Box a -> String
showBox = parens . show

mapBox :: (a -> b) -> Box a -> Box b
mapBox f (Box d n x xs) = Box d n (f x) [ (nnd,f v) | (nnd,v) <- xs ]

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

principal :: Box a -> Name
principal (Box _ x _ _) = x

defBox :: Box a -> [(Name, Dir)]
defBox (Box d x _ nvs) = (x,mirror d) : [ zd | (zd,_) <- nvs ]

fromBox :: Box a -> [(Side,a)]
fromBox (Box d x v nvs) = ((x, mirror d),v) : nvs

modBox :: (Side -> a -> b) -> Box a -> Box b
modBox f (Box dir x v nvs) =
  Box dir x (f (x,mirror dir) v) [ (nd,f nd v) | (nd,v) <- nvs ]

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
  support (Box dir n v nvs) = support ((n, v), nvs)
  swap (Box dir z v nvs) x y = Box dir z' v' nvs' where
    ((z',v'), nvs') = swap ((z, v), nvs) x y

--------------------------------------------------------------------------------
-- | Values

data KanType = Fill | Com
  deriving (Show, Eq)

data Val = VU
         | Ter Ter Env
         | VPi Val Val
         | VId Val Val Val

           -- tag values which are paths
         | Path Name Val
         | VExt Name Val Val Val Val

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

           -- neutral values
         | VApp Val Val -- the first Val must be neutral
         | VAppName Val Name
         | VBranch Val Val -- the second Val must be neutral
         | VVar String Dim
  deriving Eq

instance Show Val where
  show = showVal

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
  support VU                = []
  support (Ter _ e)         = support e
  support (VId a v0 v1)     = support [a,v0,v1]
  support (Path x v)        = delete x $ support v
  support (VInh v)          = support v
  support (VInc v)          = support v
  support (VPi v1 v2)       = support [v1,v2]
  support (VCon _ vs)       = support vs
  support (VSquash x v0 v1) = support (x, [v0,v1])
  support (VExt x b f g p)  = support (x, [b,f,g,p])
  support (Kan Fill a box)  = support (a, box)
  support (Kan Com a box@(Box _ n _ _)) = delete n (support (a, box))
  support (VEquivEq x a b f s t)    = support (x, [a,b,f,s,t])
           -- names x, y and values a, s, t
  support (VEquivSquare x y a s t)    = support ((x,y), [a,s,t])
  support (VPair x a v)             = support (x, [a,v])
  support (VComp box@(Box _ n _ _)) = delete n $ support box
  support (VFill x box)             = delete x $ support box
  support (VApp u v)        = support (u, v)
  support (VAppName u n)    = support (u, n)
  support (VBranch u v)     = support (u, v)
  support (VVar x d)        = support d
  support v = error ("support " ++ show v)

  swap u x y =
    let sw u = swap u x y in case u of
    VU          -> VU
    Ter t e     -> Ter t (swap e x y)
    VId a v0 v1 -> VId (sw a) (sw v0) (sw v1)
    Path z v | z /= x && z /= y    -> Path z (sw v)
             | otherwise -> let z' = fresh ([x, y], v)
                                v' = swap v z z'
                            in Path z' (sw v')
    VExt z b f g p  -> VExt (swap z x y) (sw b) (sw f) (sw g) (sw p)
    VPi a f         -> VPi (sw a) (sw f)
    VInh v          -> VInh (sw v)
    VInc v          -> VInc (sw v)
    VSquash z v0 v1 -> VSquash (swap z x y) (sw v0) (sw v1)
    VCon c us       -> VCon c (map sw us)
    VEquivEq z a b f s t ->
      VEquivEq (swap z x y) (sw a) (sw b) (sw f) (sw s) (sw t)
    VPair z a v  -> VPair (swap z x y) (sw a) (sw v)
    VEquivSquare z w a s t ->
      VEquivSquare (swap z x y) (swap w x y) (sw a) (sw s) (sw t)
    VSquare z w v -> VSquare (swap z x y) (swap w x y) (sw v)
    Kan Fill a b  -> Kan Fill (sw a) (swap b x y)
    Kan Com a b@(Box _ z _ _)
      | z /= x && z /= y -> Kan Com (sw a) (swap b x y)
      | otherwise -> let z' = fresh ([x, y], u)
                         a' = swap a z z'
                     in sw (Kan Com a' (swap b z z'))
    VComp b@(Box _ z _ _)
      | z /= x && z /= y -> VComp (swap b x y)
      | otherwise -> let z' = fresh ([x, y], u)
                     in sw (VComp (swap b z z'))
    VFill z b@(Box dir n _ _)
      | z /= x && z /= x -> VFill z (swap b x y)
      | otherwise        -> let
        z' = fresh ([x, y], b)
        in sw (VFill z' (swap b z z'))
    VApp u v        -> VApp (sw u) (sw v)
    VAppName u n    -> VAppName (sw u) (swap n x y) 
    VBranch u v     -> VBranch (sw u) (sw v)
    VVar s d        -> VVar s (swap d x y)

--------------------------------------------------------------------------------
-- | Environments

data Env = Empty
         | Pair Env (Binder,Val)
         | PDef [(Binder,Ter)] Env
  deriving Eq

instance Show Env where
  show = showEnv

showEnv :: Env -> String
showEnv Empty            = ""
showEnv (Pair env (x,u)) = parens $ showEnv1 env ++ show u
showEnv (PDef xas env)   = showEnv env

showEnv1 :: Env -> String
showEnv1 Empty            = ""
showEnv1 (Pair env (x,u)) = showEnv1 env ++ show u ++ ", "
showEnv1 (PDef xas env)   = show env

instance Nominal Env where
  swap e x y = mapEnv (\u -> swap u x y) e

  support Empty          = []
  support (Pair e (_,v)) = support (e, v)
  support (PDef _ e)     = support e

upds :: Env -> [(Binder,Val)] -> Env
upds = foldl Pair

mapEnv :: (Val -> Val) -> Env -> Env
mapEnv _ Empty          = Empty
mapEnv f (Pair e (x,v)) = Pair (mapEnv f e) (x,f v)
mapEnv f (PDef ts e)    = PDef ts (mapEnv f e)

valOfEnv :: Env -> [Val]
valOfEnv Empty            = []
valOfEnv (Pair env (_,v)) = v:(valOfEnv env)
valOfEnv (PDef _ env)     = valOfEnv env

--------------------------------------------------------------------------------
-- | Pretty printing

showTer :: Ter -> String
showTer U                  = "U"
showTer (Var x)            = x
showTer (App e0 e1)        = showTer e0 <+> showTer1 e1
showTer (Pi e0 e1)         = "Pi" <+> showTers [e0,e1]
showTer (Lam x e)          = "\\" ++ x <+> "->" <+> showTer e
showTer (LSum (_,str) _)   = str
showTer (Branch (n,str) _) = str ++ show n
showTer (Undef (n,str))    = str ++ show n
showTer (Con ident ts)     = ident <+> showTers ts
showTer (Id a t s)         = "Id" <+> showTers [a,t,s]
showTer (TransU t s)       = "transport" <+> showTers [t,s]
showTer (TransURef t)      = "transportRef" <+> showTer t
showTer (Refl t)           = "refl" <+> showTer t
showTer (J a b c d e f)    = "J" <+> showTers [a,b,c,d,e,f]
showTer (JEq a b c d)      = "Jeq" <+> showTers [a,b,c,d]
showTer (Ext b f g p)      = "funExt" <+> showTers [b,f,g,p]
showTer (Inh t)            = "inh" <+> showTer t
showTer (Inc t)            = "inc" <+> showTer t
showTer (Squash a b)       = "squash" <+> showTers [a,b]
showTer (InhRec a b c d)   = "inhrec" <+> showTers [a,b,c,d]
showTer (EquivEq a b c d e) = "equivEq" <+> showTers [a,b,c,d,e]
showTer (EquivEqRef a b c) = "equivEqRef" <+> showTers [a,b,c]
showTer (TransUEquivEq a b c d e f) = "transpEquivEq" <+> showTers [a,b,c,d,e,f]
showTer (Where t defs)     = showTer t <+> "where" <+> showDefs defs
showTer (MapOnPath a b)    =  "mapOnPath" <+> showTers [a,b]

showDef :: Def -> String
showDef (x,t) = x <+> "=" <+> showTer t

showDefs :: [Def] -> String
showDefs = ccat . map showDef

showTers :: [Ter] -> String
showTers = hcat . map showTer1

showTer1 :: Ter -> String
showTer1 U          = "U"
showTer1 (Con c []) = c
showTer1 (Var x)    = x
showTer1 u          = parens $ showTer u

showVal :: Val -> String
showVal VU               = "U"
showVal (Ter t env)      = showTer t <+> show env
showVal (VId a u v)      = "Id" <+> showVal1 a <+> showVal1 u <+> showVal1 v
showVal (Path n u)       = abrack (show n) <+> showVal u
showVal (VExt n b f g p) = "funExt" <+> show n <+> showVals [b,f,g,p]
showVal (VCon c us)      = c <+> showVals us
showVal (VPi a f)        = "Pi" <+> showVals [a,f]
showVal (VInh u)         = "inh" <+> showVal1 u
showVal (VInc u)         = "inc" <+> showVal1 u
showVal (VSquash n u v)  = "squash" <+> show n <+> showVals [u,v]
showVal (Kan typ v box)  = "Kan" <+> show typ <+> showVal1 v <+> showBox box
showVal (VPair n u v)    = "vpair" <+> show n <+> showVals [u,v]
showVal (VSquare x y u)  = "vsquare" <+> show x <+> show y <+> showVal1 u
showVal (VComp box)      = "vcomp" <+> showBox box
showVal (VFill n box)    = "vfill" <+> show n <+> showBox box
showVal (VEquivEq n a b f s t) = "equivEq" <+> show n <+> showVals [a,b,f,s,t]
showVal (VEquivSquare x y a s t) =
  "equivSquare" <+> show x <+> show y <+> showVals [a,s,t]
showVal (VApp u v)        = showVal u <+> showVal1 v
showVal (VAppName u n)    = showVal u <+> "@" <+> show n
showVal (VBranch u v)     = showVal u <+> showVal1 v
showVal (VVar x d)        = show x    <+> show d

showVals :: [Val] -> String
showVals = hcat . map showVal1

showVal1 :: Val -> String
showVal1 VU          = "U"
showVal1 (VCon c []) = c
showVal1 u           = parens $ showVal u
