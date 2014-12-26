{-# LANGUAGE TupleSections #-}
module CTT where

import Control.Applicative
import Data.List
import Data.Maybe
import Pretty
import Connections

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
type Brc    = (Label,([Binder],Ter))  -- TODO: why Binder and not Ident?

-- Telescope (x1 : A1) .. (xn : An)
type Tele   = [(Binder,Ter)]

-- Labelled sum: c (x1 : A1) .. (xn : An)
type LblSum = [(Binder,Tele)]

-- Context gives type values to identifiers
type Ctxt   = [(Binder,Val)]

-- Mutual recursive definitions: (x1 : A1) .. (xn : An) and x1 = e1 .. xn = en
-- (x, type, value)
type Decls  = [(Binder,Ter,Ter)]
data ODecls = ODecls Decls
            | Opaque Binder
            | Transp Binder  deriving (Eq,Show)

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
         -- c Ms xs N0 N1 connects N0 (Ms/xs) to N1 (Ms/xs)
         | PCon Label [Ter] [Ident] Ter Ter
         | HSum Binder [HLabel]
         | HSplit Loc Ter [HBranch]
         | PN PN
  deriving Eq

data HLabel = Label Binder Tele | HLabel Binder Tele Ter Ter
  deriving (Eq,Show)

data HBranch = Branch Label [Binder] Ter -- Branch of the form: c x1 .. xn -> e
             | HBranch Label [Binder] Ter -- Branch for a path constructor
  deriving (Eq,Show)

mapHLabelToBinderTele :: [HLabel] -> [(Binder,(Tele,Ter,Ter))]
mapHLabelToBinderTele [] = []
mapHLabelToBinderTele (Label _ _ : s) = mapHLabelToBinderTele s
mapHLabelToBinderTele (HLabel n tele u v : s) = (n, (tele, u, v)) : (mapHLabelToBinderTele s)

hLabelToBinderTele :: HLabel -> (Binder,Tele)
hLabelToBinderTele (Label n tele)      = (n,tele)
hLabelToBinderTele (HLabel n tele _ _) = (n,tele)

hLabelToBinder :: HLabel -> Binder
hLabelToBinder (Label n _)      = n
hLabelToBinder (HLabel n _ _ _) = n

isLabel :: HLabel -> Bool
isLabel h@Label{} = True
isLabel _         = False

hBranchToLabel :: HBranch -> Label
hBranchToLabel (Branch l _ _) = l
hBranchToLabel (HBranch l _ _) = l

-- Primitive notions
data PN = Id | Refl | Sym

        -- (A B : U) -> Id U A B -> A -> B
        -- For TransU we only need the eqproof and the element in A is needed
        | TransU

        -- (A B : U) -> Id U A B -> B -> A
        -- For TransU we only need the eqproof and the element in A is needed
        | TransInvU

        -- (A : U) -> (a : A) -> Id A a (transport A (refl U A) a)
        -- | TransURef

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
        | Ext

        -- Ext B f g p : Id (Pi A B) f g,
        -- (p : (Pi x y:A) IdS A (Bx) x y p fx gy)
        -- | HExt

        -- EquivEq A B f s t where
        -- A, B are types, f : A -> B,
        -- s : (y : B) -> fiber f y, and
        -- t : (y : B) (z : fiber f y) -> Id (fiber f y) (s y) z
        -- where fiber f y is Sigma x : A. Id B (f x) z.
        -- | EquivEq

        -- IsoId A B f g s t where
        -- (A B : U) (f : A -> B) (g : B -> A)
	-- (s : (x:A) -> Id A (g (f x)) x)
        -- (t : (y:B) -> Id B (f (g y)) y) ->
        -- Id U A B
        | IsoId

        -- (A : U) ->
        -- Id (Id U A A) (refl U A) (isoId A A (id A) (id A) (refl A) (refl A))
        | IsoIdRef

        -- (A : U) -> (s : (y : A) -> pathTo A a) ->
        -- (t : (y : B) -> (v : pathTo A a) -> Id (path To A a) (s y) v) ->
        -- Id (Id U A A) (refl U A) (equivEq A A (id A) s t)
        | EquivEqRef

        -- (A B : U) -> (f : A -> B) (s : (y : B) -> fiber A B f y) ->
        -- (t : (y : B) -> (v : fiber A B f y) -> Id (fiber A B f y) (s y) v) ->
        -- (a : A) -> Id B (f a) (transport A B (equivEq A B f s t) a)
        | TransUEquivEq

        -- (A B : U) -> (f : A -> B) (g : B -> A)
	-- (s : (x:A) -> Id A (g (f x)) x) ->
        -- (t : (y:B) -> Id B (f (g y)) y) ->
        -- (a : A) -> Id B (f a) (transport A B (isoId A B f g s t) a)
        | TransUIsoId

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

        -- lemSimpl : (A:U) -> (a b c : A) -> (p : Id A a b) -> (q q' : Id A b c) ->
        --   Id (Id A a c) (comp A a b c p q) (comp A a b c p q') -> Id (Id A b c) q q'
        | LemSimpl

        -- transpose :  (A:U) (a0 a1:A) (u : Id A a0 a1) (b0 b1 : A) (v : Id A b0 b1)
        --              (r0 : Id A a0 b0) (r1 : Id A a1 b1) ->
        --               Square A a0 b0 a1 b1 u v r0 r1 -> Square A a0 a1 b0 b1 r0 r1 u v
        | Transpose

        -- idSElim' : (A B : U) (p : Id U A B) (x : A) (y : B)
        --            -> IdP A B p x y -> Id B (transport A B p x) y
        | IdSElim

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
mkApps (Con l us) vs           = Con l (us ++ vs)
mkApps (PCon l us ns t1 t2) vs = PCon l (us ++ vs) ns t1 t2
mkApps t ts                    = foldl App t ts

mkLams :: [String] -> Ter -> Ter
mkLams bs t = foldr Lam t [noLoc b | b <- bs]

mkWheres :: [ODecls] -> Ter -> Ter
mkWheres []     e = e
mkWheres (ODecls d:ds) e = Where (mkWheres ds e) d
mkWheres _      _  = error "mkWhere: opaque is broken, fix it!"

-- Primitive notions
primHandle :: [(Ident,Int,PN)]
primHandle =
  [("Id"            , 3,  Id           ),
   ("refl"          , 2,  Refl         ),
   ("inv"          , 4,  Sym         ),
   ("funExt"        , 5,  Ext          ),
   --("funHExt"       , 5,  HExt          ),
   ("isoId"         , 6,  IsoId        ),
   ("isoIdRef"      , 1,  IsoIdRef     ),
   ("transport"     , 4,  TransU       ),
   ("transpInv"     , 4,  TransInvU    ),
   -- ("transpIsoId"   , 7,  TransUIsoId),
   ("contrSingl"    , 4,  CSingl       ),
   -- ("transportRef"  , 2,  TransURef    ),
   ("equivEqRef"    , 3,  EquivEqRef   ),
   -- ("transpEquivEq" , 6,  TransUEquivEq),
   ("appOnPath"     , 8,  AppOnPath    ),
   ("mapOnPath"     , 6,  MapOnPath    ),
   ("lemSimpl"      , 8,  LemSimpl    ),
   ("transpose"     , 10, Transpose    ),
   ("idSElim'"      , 6, IdSElim    ),
   ("IdP"           , 5,  IdP          ),
   ("mapOnPathD"    , 6,  MapOnPathD   ),
   ("mapOnPathS"    , 10, MapOnPathS   )]

reservedNames :: [String]
reservedNames = [ s | (s,_,_) <- primHandle ]

arity :: PN -> Int
arity pn = fromMaybe 0 $ listToMaybe [n | (_,n,pn') <- primHandle, pn == pn']

mkPN :: String -> Maybe PN
mkPN s = listToMaybe [pn | (s',_,pn) <- primHandle, s == s']

--------------------------------------------------------------------------------
-- | Values

data Sign = Pos | Neg
  deriving (Eq, Show)

data HisoProj = HisoSign Sign -- Pos is f, Neg is g
              | IsSection     -- f o g = 1
              | IsRetraction  -- g o f = 1
  deriving (Show, Eq)

data Val = VU
         | Ter Ter Env
         | VPi Val Val

         -- comp ^i _{ A, ts } (a)
         | Kan Name Val (System Val) Val
         | KanUElem (System Val) Val

         | UnKan (System Hiso) Val

         | VId Val Val Val

         -- tag values which are paths
         | Path Name Val

         | VSigma Val Val
         | VSPair Val Val

         | VCon Ident [Val]

         | Glue (System Hiso) Val
         | UnGlue (System Hiso) Val
         | GlueElem (System Val) Val
         | HisoProj HisoProj Val
         | GlueLine Val Formula Formula
         | GlueLineElem Val Formula Formula

         | VExt Formula Val Val Val
         -- | VHExt Name Val Val Val Val

         -- of type U connecting a and b along x
         -- VEquivEq x a b f s t
         -- | VEquivEq Name Val Val Val Val Val

         -- names x, y and values a, s, t
         -- | VEquivSquare Name Name Val Val Val

         -- of type VEquivEq
         -- | VPair Name Val Val

         -- of type VEquivSquare
         -- | VSquare Name Name Val

         -- a value of type Kan Com VU (Box (type of values))
         -- | VComp (Box Val)

         -- a value of type Kan Fill VU (Box (type of values minus name))
         -- the name is bound
         -- | VFill Name (Box Val)

         -- Path constructors
         | VPCon Ident [Val] Formula Val Val

         -- neutral values
         | VVar String  -- [Formula]
         | VApp Val Val            -- the first Val must be neutral
         | VAppFormula Val Formula
         | VFst Val
         | VSnd Val
         | VSplit Val Val          -- the second Val must be neutral
         | VHSplit Val Val          -- the second Val must be neutral
         | UnGlueNe Val Val         -- the second Val must be neutral
         | KanNe Name Val (System Val) Val -- Neutral
         -- | VIntRec Val Val Val Val Val -- the last Val must be neutral

         -- for reification
         | VLam String Val
  deriving Eq

-- vepair :: Name -> Val -> Val -> Val
-- vepair x a b = VSPair a (Path x b)

mkVar :: Int -> Val
mkVar k = VVar ('X' : show k)

-- fstVal, sndVal, unSquare :: Val -> Val
-- fstVal (VPair _ a _)     = a
-- fstVal x                 = error $ "error fstVal: " ++ show x
-- sndVal (VPair _ _ v)     = v
-- sndVal x                 = error $ "error sndVal: " ++ show x
-- unSquare (VSquare _ _ v) = v
-- unSquare v               = error $ "unSquare bad input: " ++ show v

unCon :: Val -> [Val]
unCon (VCon _ vs) = vs
unCon (KanUElem _ u) = unCon u
unCon v           = error $ "unCon: not a constructor: " ++ show v

--------------------------------------------------------------------------------
-- | Homotopy Isomorphisms

data Hiso = Hiso { hisoA :: Val
                 , hisoB :: Val
                 , hisoF :: Val -- forward
                 , hisoG :: Val -- backward
                 , hisoS :: Val -- f has a Section: f (g y) = y
                 , hisoT :: Val -- f has a reTraction: g (f x) = x
                 }
  deriving (Eq, Show)

--------------------------------------------------------------------------------
-- | Environments

data Env = Empty
         | Pair Env (Binder,Val)
         | PDef [(Binder,Ter)] Env
  deriving Eq

instance Show Env where
  show Empty            = ""
  show (PDef xas env)   = show env
  show (Pair env (x,u)) = parens $ showEnv1 env ++ fst x ++ "=" ++ show u
    where
      showEnv1 (Pair env (x,u)) = showEnv1 env ++ fst x ++ "=" ++ show u ++ ", "
      showEnv1 e                = show e

upds :: Env -> [(Binder,Val)] -> Env
upds = foldl Pair

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

-- mapEnvM :: Applicative m => (Val -> m Val) -> Env -> m Env
-- mapEnvM _ Empty          = pure Empty
-- mapEnvM f (Pair e (x,v)) = Pair <$> mapEnvM f e <*> ( (x,) <$> f v)
-- mapEnvM f (PDef ts e)    = PDef ts <$> mapEnvM f e

-- mapOEnv :: (Val -> Val) -> OEnv -> OEnv
-- mapOEnv f (OEnv e o) = OEnv (mapEnv f e) o

-- mapOEnvM :: Applicative m => (Val -> m Val) -> OEnv -> m OEnv
-- mapOEnvM f (OEnv e o) = flip OEnv o <$> mapEnvM f e

valOfEnv :: Env -> [Val]
valOfEnv Empty            = []
valOfEnv (Pair env (_,v)) = v : valOfEnv env
valOfEnv (PDef _ env)     = valOfEnv env

-- valOfOEnv :: OEnv -> [Val]
-- valOfOEnv (OEnv e o) = valOfEnv e

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
showTer (Sum l _)     = fst l
showTer (PN pn)       = showPN pn
showTer (PCon c es _ e0 e1) = -- verbose for now
  c <+> showTers es <+> "@" <+> showTer e0 <+> "~" <+> showTer e1
showTer (HSum l _)    = fst l
showTer (HSplit l _ _)  = "hsplit" <+> show l

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
showPN pn        = case [s | (s,_,pn') <- primHandle, pn == pn'] of
  [s] -> s
  _   -> error $ "showPN: unknown primitive " ++ show pn

showDecls :: Decls -> String
showDecls defs = ccat (map (\((x,_),_,d) -> x <+> "=" <+> show d) defs)

showODecls :: ODecls -> String
showODecls (ODecls defs) = showDecls defs
showODecls (Opaque x)    = "opaque"      <+> show x
showODecls (Transp x)    = "transparent" <+> show x

showSumEnv :: Env -> String
showSumEnv Empty = ""
showSumEnv (PDef xas env) = showSumEnv env
showSumEnv (Pair env (_,u)) = showVal1 u <+> showSumEnv env


instance Show Val where
  show = showVal

showVal :: Val -> String
showVal VU                       = "U"
showVal (Ter t@Sum{} env)        = show t <+> showSumEnv env
showVal (Ter t@HSum{} env)       = show t <+> showSumEnv env
showVal (Ter t env)              = show t <+> show env
showVal (VPi a f)                = "Pi" <+> showVals [a,f]
showVal (Kan i aType ts a)       =
  "Kan" <+> show i <+> showVal1 aType <+> parens (show ts) <+> showVal1 a
showVal (KanNe i aType ts a)       =
  "KanNe" <+> show i <+> showVal1 aType <+> parens (show ts) <+> showVal1 a
showVal (KanUElem ts u)          = "KanUElem" <+> show ts <+> showVal u
showVal (UnKan ts u)             = "UnKan" <+> show ts <+> showVal u

showVal (VId a u v)              =
  "Id" <+> showVal1 a <+> showVal1 u <+> showVal1 v
showVal (Path n u)               = abrack (show n) <+> showVal u

showVal (VSPair u v)             = "pair" <+> showVals [u,v]
showVal (VSigma u v)             = "Sigma" <+> showVals [u,v]
showVal (VFst u)                 = showVal u ++ ".1"
showVal (VSnd u)                 = showVal u ++ ".2"

showVal (VVar x)                 = x
showVal (VApp u v)               = showVal u <+> showVal1 v
showVal (VAppFormula u n)        = showVal u <+> "@" <+> show n

showVal (VCon c us)             = c <+> showVals us
showVal (VSplit u v)            = showVal u <+> showVal1 v

showVal (Glue ts u)             = "Glue" <+> show ts <+> showVal u
showVal (UnGlue ts u)           = "UnGlue" <+> show ts <+> showVal u
showVal (GlueElem ts u)         = "GlueElem" <+> show ts <+> showVal u
showVal (HisoProj n e)          = "HisoProj" <+> show n <+> showVal1 e

showVal (GlueLine v phi psi)     = "GlueLine" <+> show v <+> show phi <+> show psi
showVal (GlueLineElem u phi psi) = "GlueLineElem" <+> show u <+> show phi <+> show psi

showVal (VExt phi f g p)        = "funExt" <+> show phi <+> showVals [f,g,p]

showVal (VPCon c es phi u v)     = -- not verbose for now
  c <+> showVals es <+> parens (show phi) -- <+> "@" <+> showVal u <+> "~" <+> showVal v
showVal (VHSplit u v)            = showVal u <+> showVal1 v

showVal (UnGlueNe u v)           = showVal1 u <+> showVal1 v

showVal (VLam str u)             = "\\" ++ str ++ " -> " ++ showVal u

-- showVal (VHExt n b f g p)        = "funHExt" <+> show n <+> showVals [b,f,g,p]
-- showVal (Kan Fill v box)         = "Fill" <+> showVal1 v <+> parens (show box)
-- showVal (Kan Com v box)          = "Com" <+> showVal1 v <+> parens (show box)
-- showVal (VFillN v box)           = "FillN" <+> showVal1 v <+> parens (show box)
-- showVal (VComN v box)            = "ComN" <+> showVal1 v <+> parens (show box)
-- showVal (VPair n u v)            = "vpair" <+> show n <+> showVals [u,v]
-- showVal (VSquare x y u)          = "vsquare" <+> show x <+> show y <+> showVal1 u
-- showVal (VComp box)              = "vcomp" <+> parens (show box)
-- showVal (VFill n box)            = "vfill" <+> show n <+> parens (show box)
-- showVal (VEquivEq n a b f _ _)   = "equivEq" <+> show n <+> showVals [a,b,f]
-- showVal (VEquivSquare x y a s t) =
--   "equivSquare" <+> show x <+> show y <+> showVals [a,s,t]

showDim :: Show a => [a] -> String
showDim = parens . ccat . map show

showVals :: [Val] -> String
showVals = hcat . map showVal1

showVal1 :: Val -> String
showVal1 VU          = "U"
showVal1 (VCon c []) = c
showVal1 u@(VVar{})  = showVal u
showVal1 u           = parens $ showVal u
