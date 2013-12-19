module CTT where

-- import Text.PrettyPrint
import Data.List

import qualified MTT as A

--------------------------------------------------------------------------------
-- | Pretty printing combinators. Use the same names as in the pretty library.
(<+>) :: String -> String -> String
[] <+> y  = y
x  <+> [] = x
x  <+> y  = x ++ " " ++ y

infixl 6 <+>

hcat :: [String] -> String
hcat []     = []
hcat [x]    = x
hcat (x:xs) = x <+> hcat xs

parens :: String -> String
parens p = "(" ++ p ++ ")"

-- Angled brackets, not present in pretty library.
abrack :: String -> String
abrack p = "<" ++ p ++ ">"

--------------------------------------------------------------------------------
-- | Terms

type Binder = String
type Def    = [(Binder,Ter)]  -- without type annotations for now
type Ident  = String

data Ter = Var Binder
         | Id Ter Ter Ter | Refl Ter
         | Pi Ter Ter     | Lam Binder Ter | App Ter Ter
         | Where Ter Def
         | U

         | Undef A.Prim

           -- constructor c Ms
         | Con Ident [Ter]

           -- branches c1 xs1  -> M1,..., cn xsn -> Mn
         | Branch A.Prim [(Ident, ([Binder],Ter))]

           -- labelled sum c1 A1s,..., cn Ans (assumes terms are constructors)
         | LSum A.Prim [(Ident, [(Binder,Ter)])]

           -- TODO: Remove
         | TransInv Ter Ter Ter

           -- Trans type eqprof proof
           -- (Trans to be removed in favor of J ?)
           -- TODO: witness for singleton contractible and equation
         | Trans Ter Ter Ter

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
           -- TODO?: equation: InhRec p phi (Inc a) = phi a
           --                  InhRec p phi (Squash a b) =
           --                     p (InhRec p phi a) (InhRec p phi b)
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
  deriving (Show,Eq)

showTer :: Ter -> String
showTer U                  = "U"
showTer (Var x)            = "x"
showTer (App e0 e1)        = showTer e0 <+> showTer1 e1
showTer (Pi e0 e1)         = "Pi" <+> showTers [e0,e1]
showTer (Lam x e)          = "\\" ++ x ++ "." <+> showTer e
showTer (LSum (_,str) _)   = str
showTer (Branch (n,str) _) = str ++ show n
showTer (Undef (n,str))    = str ++ show n
showTer t                  = show t

-- Missing things handled by the derived show instance for now:
--   Id Ter Ter Ter
--   Refl Ter
--   Where Ter Def
--   Con Ident [Ter]
--   TransInv Ter Ter Ter
--   Trans Ter Ter Ter
--   TransU Ter Ter
--   TransURef Ter
--   J Ter Ter Ter Ter Ter Ter
--   JEq Ter Ter Ter Ter
--   Ext Ter Ter Ter Ter
--   Inh Ter
--   Inc Ter
--   Squash Ter Ter
--   InhRec Ter Ter Ter Ter
--   EquivEq Ter Ter Ter Ter Ter
--   EquivEqRef Ter Ter Ter
--   TransUEquivEq Ter Ter Ter Ter Ter Ter

showTers :: [Ter] -> String
showTers = hcat . map showTer1

showTer1 :: Ter -> String
showTer1 U          = "U"
showTer1 (Con c []) = c
showTer1 (Var x)    = x
showTer1 u          = parens $ showTer u

--------------------------------------------------------------------------------
-- | Names and dimension

type Name = Integer
type Dim  = [Name]

gensym :: Dim -> Name
gensym [] = 0
gensym xs = maximum xs + 1

gensyms :: Dim -> [Name]
gensyms d = let x = gensym d in x : gensyms (x : d)

swapName :: Name -> Name -> Name -> Name
swapName z x y | z == x    = y
               | z == y    = x
               | otherwise = z

--------------------------------------------------------------------------------
-- | Boxes

data Dir = Up | Down
  deriving (Eq, Show)

mirror :: Dir -> Dir
mirror Up   = Down
mirror Down = Up

type Side = (Name,Dir)

allDirs :: [Name] -> [Side]
allDirs []     = []
allDirs (n:ns) = (n,Down) : (n,Up) : allDirs ns

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
  Box dir x v $ ((n,Down),v0) : ((n,Up),v1) : nvs

appendBox :: [(Name,(a,a))] -> Box a -> Box a
appendBox xs b = foldr consBox b xs

appendSides :: [(Side, a)] -> Box a -> Box a
appendSides sides (Box dir x v nvs) = Box dir x v (sides ++ nvs)

transposeBox :: Box [a] -> [Box a]
transposeBox b@(Box dir _ [] _)      = []
transposeBox (Box dir x (v:vs) nvss) =
  Box dir x v [ (nnd,head vs) | (nnd,vs) <- nvss ] :
  transposeBox (Box dir x vs [ (nnd,tail vs) | (nnd,vs) <- nvss ])

supportBox :: Box Val -> [Name]
supportBox (Box dir n v vns) = [n] `union` support v `union`
  unions [ [y] `union` support v | ((y,dir'),v) <- vns ]

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
  deriving Eq

instance Show Val where
  show = showVal

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

showVals :: [Val] -> String
showVals = hcat . map showVal1

showVal1 :: Val -> String
showVal1 VU          = "U"
showVal1 (VCon c []) = c
showVal1 u           = parens $ showVal u

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

-- Compute the support of a value
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
-- TODO: test that names only occur once in support

-- TODO: Typeclass for nominal stuff
fresh :: Val -> Name
fresh = gensym . support

--------------------------------------------------------------------------------
-- | Environments

-- TODO: Almost the same as in MTT, make it more abstract?
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

upds :: Env -> [(Binder,Val)] -> Env
upds = foldl Pair

mapEnv :: (Val -> Val) -> Env -> Env
mapEnv _ Empty          = Empty
mapEnv f (Pair e (x,v)) = Pair (mapEnv f e) (x,f v)
mapEnv f (PDef ts e)    = PDef ts (mapEnv f e)

supportEnv :: Env -> [Name]
supportEnv Empty          = []
supportEnv (Pair e (_,v)) = supportEnv e `union` support v
supportEnv (PDef _ e)     = supportEnv e

freshEnv :: Env -> Name
freshEnv = gensym . supportEnv
