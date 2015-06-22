{-# LANGUAGE PatternSynonyms #-}
module CTT where

import Control.Applicative
import Pretty
import Data.List ((\\), intercalate)
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

         | CLam Binder Ter
         | CPair [Ter] Ter
         | CApp Ter CTer
         | CProj Ter Int TColor
           
           --    Γ, ∀i.Δ ⊢ t : ∀i.A
           -- --------------------------
           --    Γ,i, Δ ⊢ t@(0/i) : A@0
                 
         | CPi Ter
         | Param Ter
         | Psi (Maybe [TColor]) Ter
         | Phi Ter Ter
         | Ni Ter [Ter]
         | CU [TColor]
         | Rename CTer Ter
         | Lift Ter Ter
  deriving Eq

mkApps :: Ter -> [Ter] -> Ter
mkApps (Con l us) vs = Con l (us ++ vs)
mkApps t ts          = foldl App t ts

mkLams :: [String] -> Ter -> Ter
mkLams bs t = foldr Lam t [ noLoc b | b <- bs ]

tcpis :: [TColor] -> Ter -> Ter
tcpis [] t = t
tcpis (i:is) t = CPi $ CLam (noLoc i) $ tcpis is t

mkWheres :: [Decls] -> Ter -> Ter
mkWheres []     e = e
mkWheres (d:ds) e = Where (mkWheres ds e) d

--------------------------------------------------------------------------------
-- | Values

type TColor = String
newtype Color = Color String
  deriving Eq
instance Show Color where
     show (Color x) = x

data MCol color = Infty | Zero Int | CVar color | Max (MCol color) (MCol color)
  deriving (Eq,Show)

maxx :: MCol t -> MCol t -> MCol t
maxx (Zero i) (Zero j) = Zero (max i j)
maxx (Zero 0) x = x
maxx x (Zero 0) = x
maxx x y = Max x y
maxx Infty _ = Infty
maxx _ Infty = Infty

type CVal = MCol Color
type CTer = MCol TColor

pattern VU = VV Nothing

data Val = COLOR
         | VV (Maybe [Color])
         | VFizzle
         | Ter Ter Env
         | VPi Val Val
         | VSigma Val Val
         | VSPair Val Val
         | VCon Ident [Val]
         | VApp Val Val            -- the first Val must be neutral
         | VSplit Val Val          -- the second Val must be neutral
         | VVar String
         | VFst Val
         | VSnd Val

         | VCApp Val CVal
         | VCPi Val
         | VCLam Color Val

         | VCPair [Val] Val
         | VParam Val
         | VPsi Val
         | VPhi Val Val
         | VNi Val [Val]
         | VLam (Val -> Val)
         | VConstr CVal Val -- Deprec.
         | VLift Val Val
  -- deriving Eq

class Nominal a where
  support :: a -> [String]

instance Nominal () where
  support () = []

instance Nominal Loc where
  support _ = []

instance Nominal Color where
  support (Color x) = [x]
instance (Nominal a, Nominal b) => Nominal (a,b) where support (a,b) = support a ++ support b
instance (Nominal a) => Nominal [a] where support = concatMap support
instance (Nominal a) => Nominal (Maybe a) where
  support (Just x) = support x
  support Nothing = []

instance (Nominal a) => Nominal (MCol a) where
  support (Zero _) = []
  support (CVar a) = support a
  support (Max a b) = support (a,b)
  support Infty = []

instance Nominal Val where
  support v0 = case v0 of
    VV cs -> support cs
    VPi a b -> support (a,b)
    VSigma a b -> support (a,b)
    VSPair a b -> support (a,b)
    VCPair a b -> support (a,b)
    VPhi a b -> support (a,b)
    VNi a b -> support (a,b)
    VCon _ vs -> support vs
    VApp a p ->  support (a,p)
    VSplit a p ->  support (a,p)
    VVar x -> []
    VFizzle -> []
    VFst a -> support a
    VSnd a -> support a
    VParam a -> support a
    VPsi a -> support a
    VCPi a -> support a
    VCApp a c -> support (a,c)
    VCLam i a -> support (i,a)
    VLam f -> support (f $ VVar "__SUPPORT__")
    VConstr c a -> support (c,a)
    Ter x e -> support (x,e)

fresh a = x0 where (x0:_) = namesFrom "ijk" \\ support a

mkVar :: Int -> Val
mkVar k = VVar ('X' : show k)

mkCol :: Int -> CVal
mkCol k = CVar $ Color ('C' : show k)

isNeutral :: Val -> Bool
isNeutral (VCPair _ _) = True -- ?????
isNeutral (VCApp u _) = isNeutral u
isNeutral (VApp u _)   = isNeutral u
isNeutral (VSplit _ v) = isNeutral v
isNeutral (VVar _)     = True
isNeutral (VFst v)     = isNeutral v
isNeutral (VSnd v)     = isNeutral v
isNeutral _            = False

--------------------------------------------------------------------------------
-- | Environments

data Env = Empty
         | Pair Env (Binder,Val)
         | PDef [(Binder,Ter)] Env
         | PCol Env (Binder,CVal)
  -- deriving Eq

instance Nominal Env where
  support e0 = case e0 of
    Empty -> []
    Pair e (_,v) -> support (e,v)
    PDef ds e -> support (map snd ds,e)
    PCol e (_,v) -> support (e,v)

instance Nominal Ter where
  support _ = []
  
instance Show Env where
  show e0 = case e0 of
    Empty            -> ""
    (PDef xas env)   -> show env
    (Pair env ((x,_),u)) -> show env ++ ", " ++ show (x,u)
    (PCol env ((x,_),u)) -> show env ++ show (x,u)

upds :: Env -> [(Binder,Val)] -> Env
upds = foldl Pair

lookupIdent :: Ident -> [(Binder,a)] -> Maybe (Binder, a)
lookupIdent x defs = lookup x [ (y,((y,l),t)) | ((y,l),t) <- defs]

getIdent :: Ident -> [(Binder,a)] -> Maybe a
getIdent x defs = snd <$> lookupIdent x defs

valOfEnv :: Env -> [Val]
valOfEnv Empty            = []
valOfEnv (Pair env (_,v)) = v : valOfEnv env
valOfEnv (PDef _ env)     = valOfEnv env
valOfEnv (PCol env (_,v)) = VCApp (VVar "__valOfEnv__") v : valOfEnv env

--------------------------------------------------------------------------------
-- | Pretty printing

instance Show Loc where
  show (Loc name (i,j)) = name ++ "_L" ++ show i ++ "_C" ++ show j

instance Show Ter where
  show = showTer

showCol :: Show color => MCol color -> String
showCol (Zero i)  = show i
showCol Infty  = " ∞ "
showCol (CVar x) = show x
showCol (Max x y) = showCol x ++ " ⊔ " ++ showCol y

showConstr :: Show color => MCol color -> [Char]
showConstr xs =  "[" ++ showCol xs ++ ">0]"

showTer :: Ter -> String
showTer U             = "U"
showTer (CU cs)             = "#" ++ concat cs
showTer (App e0 e1)   = showTer e0 <+> showTer1 e1
showTer (CApp e0 e1)   = showTer e0 <+> "@" <+> showCol e1
showTer (CProj e0 p i)   = showTer e0 <+> "/" ++ show p ++ "/" ++ show i
showTer (Rename i t)   = showTer t <+> "/" <+> showCol i
showTer (Pi e0 e1)    = "Pi" <+> showTers [e0,e1]
showTer (CPi e) = "Pi" <+> showTer e
showTer (Lam (x,_) e) = '\\' : x <+> "->" <+> showTer e
showTer (CLam (x,_) e) = "<" ++ x ++ ">" <+> showTer e
showTer (Fst e)       = showTer e ++ ".1"
showTer (Snd e)       = showTer e ++ ".2"
showTer (Param e)       = showTer e ++ "!"
showTer (Phi f g)       = "phi" <+> showTers [f,g]
showTer (Psi _ e)       = "PSI" <+> showTer e
showTer (Sigma e0 e1) = "Sigma" <+> showTers [e0,e1]
showTer (SPair e0 e1) = "pair" <+> showTers [e0,e1]
showTer (CPair e0 e1) = "[" <+> showTerss e0 <+> "," <+> showTer e1 <+>"]"
showTer (Where e d)   = showTer e <+> "where" <+> showDecls d
showTer (Var x)       = x
showTer (Con c es)    = c <+> showTers es
showTer (Split l _)   = "split " ++ show l
showTer (Sum l _)     = "sum " ++ show l
showTer (Undef _)     = "undefined (1)"
showTer (Ni f a)    = showTer f ++ " ? " ++ showTerss a

showTers :: [Ter] -> String
showTers = hcat . map showTer1

showTerss :: [Ter] -> String
showTerss = parens . intercalate "&" . map showTer

showTer1 :: Ter -> String
showTer1 U           = "U"
showTer1 (Con c [])  = c
showTer1 (Var x)     = x
showTer1 u@(Split{}) = showTer u
showTer1 u@(Sum{})   = showTer u
showTer1 u           = parens $ showTer u

showDecls :: Decls -> String
showDecls defs = ccat (map (\((x,_),_,d) -> x <+> "=" <+> show d) defs)

namesFrom :: [Char] -> [[Char]]
namesFrom xs = [x ++ n | n <- "":map show [(1::Int)..], x <- map (:[]) xs]

instance Show Val where
  show = showVal $ namesFrom ['α'..'ω']

showVal :: [String] -> Val -> String
showVal su@(s:ss) t0 = case t0 of
  COLOR -> "COLOR"
  VV Nothing           -> "U"
  VV (Just cs)           -> "#(" ++ concatMap show cs ++ ")"
  (Ter t env)  -> show t <+> show env
  (VCon c us)  -> c <+> showVals su us
  (VCLam i f)  -> "<" ++ show i ++ ">" <+> showVal ss f
  (VLam f)  -> "\\" ++ s ++ " -> " <+> showVal ss (f $ VVar s)
  (VPi a f)    -> "Pi" <+> svs [a,f]
  (VCPi f)    -> "PI" <+> sv f
  (VApp u v)   -> sv u <+> sv1 v
  (VCApp u i)   -> sv1 u <+> "@" ++ showCol i
  (VSplit u v) -> sv u <+> sv1 v
  (VVar x)     -> x
  (VSPair u v) -> "pair" <+> svs [u,v]
  (VCPair u v) -> sss u <+> sv v
  (VSigma u v) -> "Sigma" <+> svs [u,v]
  (VFst u)     -> sv u ++ ".1"
  (VSnd u)     -> sv u ++ ".2"
  (VParam u)     -> sv1 u ++ "!"
  (VPsi u)     -> "PSI" ++ sv u
  (VPhi t u)     -> "Phi" <+> svs [t,u]
  (VNi f a)    -> sv1 f ++ " ? " ++ sss a
  (VConstr c a)    -> showConstr c ++ sv a
 where sv = showVal su
       sv1 = showVal1 su
       svs = showVals su
       sss =  parens . intercalate "&" . map (showVal su)

showDim :: Show a => [a] -> String
showDim = parens . ccat . map show

showVals :: [String] -> [Val] -> String
showVals su = hcat . map (showVal1 su)

showVal1 :: [String] -> Val -> String
showVal1 _ VU          = "U"
showVal1 _ VFizzle          = "#"
showVal1 _ (VCon c []) = c
showVal1 su u@(VVar{})  = showVal su u
showVal1 su u           = parens $ showVal su u
