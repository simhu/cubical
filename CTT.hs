{-# LANGUAGE TupleSections #-}
module CTT where

import Control.Applicative
import Data.List
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
data ODecls = ODecls        Decls
            | Opaque        Binder
            | Transparent   Binder
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
         | ColoredSigma Color Ter Ter
         | ColoredPair Color Ter Ter
         | ColoredSnd Color Ter
         | Where Ter ODecls
         | Var Ident
         | U
         -- constructor c Ms
         | Con Label [Ter]
         -- branches c1 xs1  -> M1,..., cn xsn -> Mn
         | Split Loc [Brc]
         -- labelled sum c1 A1s,..., cn Ans (assumes terms are constructors)
         | Sum Loc LblSum
  deriving Eq

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

--------------------------------------------------------------------------------
-- | Names, dimension, and nominal type class

-- type Name = Integer
newtype Name = N String
  deriving (Eq,Ord)
type Color = Name

instance Show Name where
  show (N s) = s

type Dim = [CVal]
type CVal = Maybe Color
  
allStrings :: [String]
allStrings = [] : [x:s | s <- allStrings, x <- ['a'..'z']]

allSyms :: [Name]
allSyms = tail $ map N allStrings

gensym :: [Name] -> Name
gensym xs = head $ gensyms xs

gensyms :: [Name] -> [Name]
gensyms d = allSyms \\ d

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

instance (Nominal a, Nominal b, Nominal c) => Nominal (a, b,c) where
  support (a,b,c)  = support ((a,b),c)
  swap (a,b,c) x y = (swap a x y, swap b x y, swap c x y)

instance Nominal a => Nominal [a]  where
  support vs  = unions (map support vs)
  swap vs x y = [swap v x y | v <- vs]

-- Make Name an instance of Nominal
instance Nominal Name where
  support n = [n]

  swap z x y | z == x    = y
             | z == y    = x
             | otherwise = z

instance Nominal a => Nominal (Maybe a) where
  support Nothing = []
  support (Just x) = support x
  swap Nothing _ _ = Nothing
  swap (Just x) i j = Just $ swap x i j

type Dir = Integer
type Side = (Name,Dir)

sequenceSnd :: Monad m => [(a,m b)] -> m [(a,b)]
sequenceSnd []          = return []
sequenceSnd ((a,b):abs) = do
  b' <- b
  acs <- sequenceSnd abs
  return $ (a,b') : acs

--------------------------------------------------------------------------------
-- | Values

data Val = VU
         | Ter Ter OEnv
         | VPi Val Val

         | VSigma Val Val
         | VSPair Val Val

         | VCSigma Color Val Val
         | VCSPair Color Val Val

         | VCon Ident [Val]

         -- neutral values
         | VApp Val Val            -- the first Val must be neutral
         | VAppName Val Name
         | VSplit Val Val          -- the second Val must be neutral
         | VVar String Dim
         | VFst Val
         | VSnd Val
         | VCSnd Color Val
  deriving Eq

mkVar :: Int -> [Name] -> Val
mkVar k ns = VVar ('X' : show k) (map Just ns)

isNeutral :: Val -> Bool
isNeutral (VApp u _)     = isNeutral u
isNeutral (VAppName u _) = isNeutral u
isNeutral (VSplit _ v)   = isNeutral v
isNeutral (VVar _ _)     = True
isNeutral (VFst v)       = isNeutral v
isNeutral (VSnd v)       = isNeutral v
isNeutral (VCSnd _i v)   = isNeutral v
isNeutral _              = False

unions :: Eq a => [[a]] -> [a]
unions = foldr union []

instance Nominal Val where
  support VU              = []
  support (Ter _ e)       = support e
  support (VPi v1 v2)     = support [v1,v2]
  support (VCon _ vs)     = support vs
  support (VApp u v)      = support (u, v)
  support (VAppName u n)  = support (u, n)
  support (VSplit u v)    = support (u, v)
  support (VVar _x d)     = support d
  support (VSigma u v)    = support (u,v)
  support (VSPair u v)    = support (u,v)
  support (VCSigma i u v) = support (i,u,v)
  support (VCSPair i u v) = support (i,u,v)
  support (VFst u)        = support u
  support (VSnd u)        = support u
  support (VCSnd i u)     = delete i $ support u
  -- support v               = error ("support " ++ show v)

  swap u x y = case u of
    VU                           -> VU
    Ter t e                      -> Ter t (swap e x y)
    VPi a f                      -> VPi (sw a) (sw f)
    VCon c us                    -> VCon c (map sw us)
    VApp u v                     -> VApp (sw u) (sw v)
    VAppName u n                 -> VAppName (sw u) (swap n x y)
    VSplit u v                   -> VSplit (sw u) (sw v)
    VVar s d                     -> VVar s (swap d x y)
    VSigma u v                   -> VSigma (sw u) (sw v)
    VSPair u v                   -> VSPair (sw u) (sw v)
    VCSigma i u v                -> VCSigma (sw i) (sw u) (sw v)
    VCSPair i u v                -> VCSPair (sw i) (sw u) (sw v)
    VFst u                       -> VFst (sw u)
    VSnd u                       -> VSnd (sw u)
    VCSnd z u | z /= x && z /= y -> VCSnd z (sw u)
              | otherwise        -> let z' = fresh ([x, y], u)
                                        v  = swap u z z'
                                    in VCSnd z' (sw v)
   where sw u = swap u x y


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
oPDef True (Transparent d) (OEnv e o) = OEnv e (d `delete` o)
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
getIdent x defs = snd <$> lookupIdent x defs

getBinder :: Ident -> [(Binder,a)] -> Maybe Binder
getBinder x defs = fst <$> lookupIdent x defs

mapEnv :: (Val -> Val) -> Env -> Env
mapEnv _ Empty          = Empty
mapEnv f (Pair e (x,v)) = Pair (mapEnv f e) (x,f v)
mapEnv f (PDef ts e)    = PDef ts (mapEnv f e)

mapEnvM :: Applicative m => (Val -> m Val) -> Env -> m Env
mapEnvM _ Empty          = pure Empty
mapEnvM f (Pair e (x,v)) = Pair <$> mapEnvM f e <*> ( (x,) <$> f v)
mapEnvM f (PDef ts e)    = PDef ts <$> mapEnvM f e

mapOEnv :: (Val -> Val) -> OEnv -> OEnv
mapOEnv f (OEnv e o) = (OEnv (mapEnv f e) o)

mapOEnvM :: Applicative m => (Val -> m Val) -> OEnv -> m OEnv
mapOEnvM f (OEnv e o) = flip OEnv o <$> (mapEnvM f e)

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
showTer U                      = "U"
showTer (App e0 e1)            = showTer e0 <+> showTer1 e1
showTer (Pi e0 e1)             = "Pi" <+> showTers [e0,e1]
showTer (Lam (x,_) e)          = '\\' : x <+> "->" <+> showTer e
showTer (Fst e)                = showTer e ++ ".1"
showTer (Snd e)                = showTer e ++ ".2"
showTer (Sigma e0 e1)          = "Sigma" <+> showTers [e0,e1]
showTer (SPair e0 e1)          = "pair" <+> showTers [e0,e1]
showTer (ColoredSnd i e)       = showTer e ++ "." ++ show i
showTer (ColoredSigma i e0 e1) = ("CSigma" ++ show i) <+> showTers [e0,e1]
showTer (ColoredPair i e0 e1)  = ("Cpair" ++ show i) <+> showTers [e0,e1]
showTer (Where e d)            = showTer e <+> "where" <+> showODecls d
showTer (Var x)                = x
showTer (Con c es)             = c <+> showTers es
showTer (Split l _)            = "split " ++ show l
showTer (Sum l _)              = "sum " ++ show l

showTers :: [Ter] -> String
showTers = hcat . map showTer1

showTer1 :: Ter -> String
showTer1 U           = "U"
showTer1 (Con c [])  = c
showTer1 (Var x)     = x
showTer1 u@(Split{}) = showTer u
showTer1 u@(Sum{})   = showTer u
showTer1 u           = parens $ showTer u

showDecls :: Decls -> String
showDecls defs = ccat (map (\((x,_),_,d) -> x <+> "=" <+> show d) defs)

showODecls :: ODecls -> String
showODecls (ODecls defs)   = showDecls defs
showODecls (Opaque x)      = "opaque"      ++ show x
showODecls (Transparent x) = "transparent" ++ show x

instance Show Val where
  show = showVal

showVal :: Val -> String
showVal VU              = "U"
showVal (Ter t env)     = show t <+> show env
showVal (VApp u v)      = showVal u <+> showVal1 v
showVal (VAppName u n)  = showVal u <+> "@" <+> show n
showVal (VSplit u v)    = showVal u <+> showVal1 v
showVal (VVar x d)      = x <+> showDim d
showVal (VSPair u v)    = "pair" <+> showVals [u,v]
showVal (VSigma u v)    = "Sigma"<+> showVals [u,v]
showVal (VCSPair i u v) = "Cpair" ++ show i  <+> showVals [u,v]
showVal (VCSigma i u v) = "CSigma"  ++ show i <+> showVals [u,v]
showVal (VFst u)        = showVal u ++ ".1"
showVal (VSnd u)        = showVal u ++ ".2"
showVal (VCSnd i u)     = showVal u ++ "." ++ show i

showDim :: Show a => [a] -> String
showDim = parens . ccat . map show

showVals :: [Val] -> String
showVals = hcat . map showVal1

showVal1 :: Val -> String
showVal1 VU           = "U"
showVal1 (VCon c [])  = c
showVal1 u@(VVar{})   = showVal u
showVal1 u            = parens $ showVal u
