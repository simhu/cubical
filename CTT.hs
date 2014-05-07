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
         | Where Ter Decls
         | Var Ident
         | U
         -- constructor c Ms
         | Con Label [Ter]
         -- branches c1 xs1  -> M1,..., cn xsn -> Mn
         | Split Loc [Brc]
         -- labelled sum c1 A1s,..., cn Ans (assumes terms are constructors)
         | Sum Binder LblSum
         | Undef Loc
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

mkWheres :: [Decls] -> Ter -> Ter
mkWheres []     e = e
mkWheres (d:ds) e = Where (mkWheres ds e) d

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
-- | Values

data Val = VU
         | Ter Ter Env
         | VPi Val Val
         | VId Val Val Val
         | VSigma Val Val
         | VSPair Val Val
         | VCon Ident [Val]
         -- neutral values
         | VApp Val Val            -- the first Val must be neutral
         | VSplit Val Val          -- the second Val must be neutral
         | VVar String Dim
         | VFst Val
         | VSnd Val
  deriving Eq

mkVar :: Int -> Dim -> Val
mkVar k = VVar ('X' : show k)

isNeutral :: Val -> Bool
isNeutral (VApp u _)   = isNeutral u
isNeutral (VSplit _ v) = isNeutral v
isNeutral (VVar _ _)   = True
isNeutral (VFst v)     = isNeutral v
isNeutral (VSnd v)     = isNeutral v
isNeutral _            = False

unCon :: Val -> [Val]
unCon (VCon _ vs) = vs
unCon v           = error $ "unCon: not a constructor: " ++ show v

unions :: Eq a => [[a]] -> [a]
unions = foldr union []

instance Nominal Val where
  support VU            = []
  support (Ter _ e)     = support e
  support (VId a v0 v1) = support [a,v0,v1]
  support (VPi v1 v2)   = support [v1,v2]
  support (VCon _ vs)   = support vs
  support (VApp u v)    = support (u, v)
  support (VSplit u v)  = support (u, v)
  support (VVar x d)    = support d
  support (VSigma u v)  = support (u,v)
  support (VSPair u v)  = support (u,v)
  support (VFst u)      = support u
  support (VSnd u)      = support u
--  support v                    = error ("support " ++ show v)

  swap u x y =
    let sw u = swap u x y in case u of
    VU          -> VU
    Ter t e     -> Ter t (swap e x y)
    VId a v0 v1 -> VId (sw a) (sw v0) (sw v1)
    VPi a f     -> VPi (sw a) (sw f)
    VCon c us   -> VCon c (map sw us)
    VApp u v    -> VApp (sw u) (sw v)
    VSplit u v  -> VSplit (sw u) (sw v)
    VVar s d    -> VVar s (swap d x y)
    VSigma u v  -> VSigma (sw u) (sw v)
    VSPair u v  -> VSPair (sw u) (sw v)
    VFst u      -> VFst (sw u)
    VSnd u      -> VSnd (sw u)

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

upds :: Env -> [(Binder,Val)] -> Env
upds = foldl Pair

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

valOfEnv :: Env -> [Val]
valOfEnv Empty            = []
valOfEnv (Pair env (_,v)) = v : valOfEnv env
valOfEnv (PDef _ env)     = valOfEnv env

--------------------------------------------------------------------------------
-- | Pretty printing

instance Show Loc where
  show (Loc name (i,j)) = name ++ "_L" ++ show i ++ "_C" ++ show j

instance Show Ter where
  show = showTer

showTer :: Ter -> String
showTer U             = "U"
showTer (App e0 e1)   = showTer e0 <+> showTer1 e1
showTer (Pi e0 e1)    = "Pi" <+> showTers [e0,e1]
showTer (Lam (x,_) e) = '\\' : x <+> "->" <+> showTer e
showTer (Fst e)       = showTer e ++ ".1"
showTer (Snd e)       = showTer e ++ ".2"
showTer (Sigma e0 e1) = "Sigma" <+> showTers [e0,e1]
showTer (SPair e0 e1) = "pair" <+> showTers [e0,e1]
showTer (Where e d)   = showTer e <+> "where" <+> showDecls d
showTer (Var x)       = x
showTer (Con c es)    = c <+> showTers es
showTer (Split l _)   = "split " ++ show l
showTer (Sum l _)     = "sum " ++ show l
showTer (Undef _)     = "undefined"

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

instance Show Val where
  show = showVal

showVal :: Val -> String
showVal VU           = "U"
showVal (Ter t env)  = show t <+> show env
showVal (VId a u v)  = "Id" <+> showVal1 a <+> showVal1 u <+> showVal1 v
showVal (VCon c us)  = c <+> showVals us
showVal (VPi a f)    = "Pi" <+> showVals [a,f]
showVal (VApp u v)   = showVal u <+> showVal1 v
showVal (VSplit u v) = showVal u <+> showVal1 v
showVal (VVar x d)   = x <+> showDim d
showVal (VSPair u v) = "pair" <+> showVals [u,v]
showVal (VSigma u v) = "Sigma" <+> showVals [u,v]
showVal (VFst u)     = showVal u ++ ".1"
showVal (VSnd u)     = showVal u ++ ".2"

showDim :: Show a => [a] -> String
showDim = parens . ccat . map show

showVals :: [Val] -> String
showVals = hcat . map showVal1

showVal1 :: Val -> String
showVal1 VU          = "U"
showVal1 (VCon c []) = c
showVal1 u@(VVar{})  = showVal u
showVal1 u           = parens $ showVal u
