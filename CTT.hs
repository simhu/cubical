module CTT where

import Control.Applicative
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
         | CPair Ter Ter
         | CApp Ter CVal
         | CPi Ter
         | Param Ter
         | Psi Ter
         | Ni Ter Ter
  deriving Eq

mkApps :: Ter -> [Ter] -> Ter
mkApps (Con l us) vs = Con l (us ++ vs)
mkApps t ts          = foldl App t ts

mkLams :: [String] -> Ter -> Ter
mkLams bs t = foldr Lam t [ noLoc b | b <- bs ]

mkWheres :: [Decls] -> Ter -> Ter
mkWheres []     e = e
mkWheres (d:ds) e = Where (mkWheres ds e) d

--------------------------------------------------------------------------------
-- | Values

type Color = String
data CVal = Zero | CVar Color
  deriving Eq

data Val = VU
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
         | VCLam (CVal -> Val)

         | VCPair Val Val
         | VParam Val
         | VPsi Val
         | VNi Val Val
  -- deriving Eq

mkVar :: Int -> Val
mkVar k = VVar ('X' : show k)

isNeutral :: Val -> Bool
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
  -- deriving Eq

instance Show Env where
  show Empty            = ""
  show (PDef xas env)   = show env
  show (Pair env (x,u)) = parens $ showEnv1 env ++ show u
    where
      showEnv1 (Pair env (x,u)) = showEnv1 env ++ show u ++ ", "
      showEnv1 e                = show e

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

--------------------------------------------------------------------------------
-- | Pretty printing

instance Show Loc where
  show (Loc name (i,j)) = name ++ "_L" ++ show i ++ "_C" ++ show j

instance Show Ter where
  show = showTer

showCol :: CVal -> String
showCol Zero  = "0"
showCol (CVar x) = x

showTer :: Ter -> String
showTer U             = "U"
showTer (App e0 e1)   = showTer e0 <+> showTer1 e1
showTer (CApp e0 e1)   = showTer e0 <+> "@" <+> showCol e1
showTer (Pi e0 e1)    = "Pi" <+> showTers [e0,e1]
showTer (CPi e) = "Pi" <+> showTer e
showTer (Lam (x,_) e) = '\\' : x <+> "->" <+> showTer e
showTer (CLam (x,_) e) = "<" ++ x ++ ">" <+> showTer e
showTer (Fst e)       = showTer e ++ ".1"
showTer (Snd e)       = showTer e ++ ".2"
showTer (Param e)       = showTer e ++ "!"
showTer (Psi e)       = "PSI" <+> showTer e
showTer (Sigma e0 e1) = "Sigma" <+> showTers [e0,e1]
showTer (SPair e0 e1) = "pair" <+> showTers [e0,e1]
showTer (CPair e0 e1) = "[" <+> showTer e0 <+> "," <+> showTer e1 <+>"]"
showTer (Where e d)   = showTer e <+> "where" <+> showDecls d
showTer (Var x)       = x
showTer (Con c es)    = c <+> showTers es
showTer (Split l _)   = "split " ++ show l
showTer (Sum l _)     = "sum " ++ show l
showTer (Undef _)     = "undefined"
showTer (Ni f a)    = showTer f ++ " ? " ++ showTer1 a

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
showVal (VCon c us)  = c <+> showVals us
showVal (VCLam f)  = "<>" <+> showVal (f $ CVar "*")
showVal (VPi a f)    = "Pi" <+> showVals [a,f]
showVal (VCPi f)    = "PI" <+> showVal f
showVal (VApp u v)   = showVal u <+> showVal1 v
showVal (VCApp u i)   = showVal u <+> "@" ++ showCol i
showVal (VSplit u v) = showVal u <+> showVal1 v
showVal (VVar x)     = x
showVal (VSPair u v) = "pair" <+> showVals [u,v]
showVal (VCPair u v) = "cpair" <+> showVals [u,v]
showVal (VSigma u v) = "Sigma" <+> showVals [u,v]
showVal (VFst u)     = showVal u ++ ".1"
showVal (VSnd u)     = showVal u ++ ".2"
showVal (VParam u)     = showVal u ++ "!"
showVal (VPsi u)     = "PSI" ++ showVal u
showVal (VNi f a)    = showVal f ++ " ? " ++ showVal a

showDim :: Show a => [a] -> String
showDim = parens . ccat . map show

showVals :: [Val] -> String
showVals = hcat . map showVal1

showVal1 :: Val -> String
showVal1 VU          = "U"
showVal1 (VCon c []) = c
showVal1 u@(VVar{})  = showVal u
showVal1 u           = parens $ showVal u
