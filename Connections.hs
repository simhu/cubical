{-# LANGUAGE TypeSynonymInstances, FlexibleInstances,
             GeneralizedNewtypeDeriving #-}
module Connections where

import Control.Applicative
import Data.List
import Data.Map (Map,(!))
import Data.Set (Set)
import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.Maybe
import Test.QuickCheck

newtype Name = Name Integer
  deriving (Arbitrary,Eq,Ord)

instance Show Name where
  show (Name i) = 'i' : show i

swapName :: Name -> (Name,Name) -> Name
swapName k (i,j) | k == i    = j
                 | k == j    = i
                 | otherwise = k


-- | Directions
data Dir = Zero | One
  deriving (Eq,Ord)

instance Show Dir where
  show Zero = "0"
  show One  = "1"

instance Num Dir where
  Zero + Zero = Zero
  _    + _    = One

  Zero * _ = Zero
  One  * x = x

  abs      = id
  signum _ = One

  negate Zero = One
  negate One  = Zero

  fromInteger 0 = Zero
  fromInteger 1 = One
  fromInteger _ = error "fromInteger Dir"

instance Arbitrary Dir where
  arbitrary = do
    b <- arbitrary
    return $ if b then Zero else One

-- | Face

-- Faces of the form: [(i,0),(j,1),(k,0)]
type Face = Map Name Dir

instance Arbitrary Face where
  arbitrary = Map.fromList <$> arbitrary

swapFace :: Face -> (Name,Name) -> Face
swapFace alpha ij = Map.mapKeys (`swapName` ij) alpha

-- i,j,k,l :: Name
-- i = Name 0
-- j = Name 1
-- k = Name 2
-- l = Name 3

-- f1,f2 :: Face
-- f1 = Map.fromList [(i,0),(j,1),(k,0)]
-- f2 = Map.fromList [(i,0),(j,1),(l,1)]

-- Check if two faces are compatible
compatible :: Face -> Face -> Bool
compatible xs ys = and (Map.elems (Map.intersectionWith (==) xs ys))

compatibles :: [Face] -> Bool
compatibles []     = True
compatibles (x:xs) = all (x `compatible`) xs && compatibles xs

-- Partial composition operation
meet :: Face -> Face -> Face
meet = Map.unionWith f
  where f d1 d2 = if d1 == d2 then d1 else error "meet: incompatible faces"

meetMaybe :: Face -> Face -> Maybe Face
meetMaybe x y = if compatible x y then Just $ meet x y else Nothing

meetCom :: Face -> Face -> Property
meetCom xs ys = compatible xs ys ==> xs `meet` ys == ys `meet` xs

meetAssoc :: Face -> Face -> Face -> Property
meetAssoc xs ys zs = compatibles [xs,ys,zs] ==>
                     xs `meet` (ys `meet` zs) == (xs `meet` ys) `meet` zs

meetId :: Face -> Bool
meetId xs = xs `meet` xs == xs

meets :: [Face] -> [Face] -> [Face]
meets xs ys = nub [ meet x y | x <- xs, y <- ys, compatible x y ]

-- instance Ord Face where

leq :: Face -> Face -> Bool
alpha `leq` beta = meetMaybe alpha beta == Just alpha

comparable :: Face -> Face -> Bool
comparable alpha beta = alpha `leq` beta || beta `leq` alpha

incomparables :: [Face] -> Bool
incomparables []     = True
incomparables (x:xs) = all (not . (x `comparable`)) xs && incomparables xs

(~>) :: Name -> Dir -> Face
i ~> d = Map.singleton i d

eps :: Face
eps = Map.empty

-- Compute the witness of A <= B, ie compute C s.t. B = CA
-- leqW :: Face -> Face -> Face
-- leqW = undefined

-- data Faces = Faces (Set Face)

-- instance Nominal Faces where
--   support (Faces f)      =
--   act (Faces f) (i, phi) = Faces f

-- | Formulas
data Formula = Dir Dir
             | Atom Name
             | NegAtom Name
             | Formula :/\: Formula
             | Formula :\/: Formula
  deriving (Eq,Show)

arbFormula :: [Name] -> Int -> Gen Formula
arbFormula names s =
      frequency [ (1, Dir <$> arbitrary)
                , (1, Atom <$> elements names)
                , (1, NegAtom <$> elements names)
                , (s, do op <- elements [andFormula,orFormula]
                         op <$> arbFormula names s' <*> arbFormula names s')
                ]
      where s' = s `div` 3

instance Arbitrary Formula where
  arbitrary = do
      n <- arbitrary :: Gen Integer
      sized $ arbFormula (map Name [0..(abs n)])

class ToFormula a where
  toFormula :: a -> Formula

instance ToFormula Formula where
  toFormula = id

instance ToFormula Name where
  toFormula = Atom

instance ToFormula Dir where
  toFormula = Dir

-- TODO: FINISH!
-- instance Show a => Show (Formula a) where
--   show Zero = "0"
--   show One  = "1"
--   show (NegAtom a)  = "~" ++ show a
--   show (Atom a) = show a
--   show (a :/\: b) = show a ++ " /\ " ++ show b

negFormula :: Formula -> Formula
negFormula (Dir b)        = Dir (- b)
negFormula (Atom i)       = NegAtom i
negFormula (NegAtom i)    = Atom i
negFormula (phi :/\: psi) = orFormula (negFormula phi) (negFormula psi)
negFormula (phi :\/: psi) = andFormula (negFormula phi) (negFormula psi)

andFormula :: Formula -> Formula -> Formula
andFormula (Dir Zero) _  = Dir Zero
andFormula _ (Dir Zero)  = Dir Zero
andFormula (Dir One) phi = phi
andFormula phi (Dir One) = phi
andFormula phi psi       = phi :/\: psi

orFormula :: Formula -> Formula -> Formula
orFormula (Dir One) _    = Dir One
orFormula _ (Dir One)    = Dir One
orFormula (Dir Zero) phi = phi
orFormula phi (Dir Zero) = phi
orFormula phi psi        = phi :\/: psi

evalFormula :: [Name] -> Formula -> Face -> Formula
evalFormula s phi alpha =
  Map.foldWithKey (\i d psi -> act s psi (i,Dir d)) phi alpha

  -- (Dir b) alpha  = Dir b
-- evalFormula (Atom i) alpha = case Map.lookup i alpha of
--                                Just b -> Dir b
--                                Nothing -> Atom i
-- evalFormula (Not phi) alpha = negFormula (evalFormula phi alpha)
-- evalFormula (phi :/\: psi) alpha =
--   andFormula (evalFormula phi alpha) (evalFormula psi alpha)
-- evalFormula (phi :\/: psi) alpha =
--   orFormula (evalFormula phi alpha) (evalFormula psi alpha)

-- find a better name?
-- phi b = max {alpha : Face | phi alpha = b}
invFormula :: Formula -> Dir -> [Face]
invFormula (Dir b') b          = [ eps | b == b' ]
invFormula (Atom i) b          = [ Map.singleton i b ]
invFormula (NegAtom i) b         = [ Map.singleton i (- b) ]
invFormula (phi :/\: psi) Zero = invFormula phi 0 `union` invFormula psi 0
invFormula (phi :/\: psi) One  =
  meets (invFormula phi 1) (invFormula psi 1)
invFormula (phi :\/: psi) b    = invFormula (negFormula phi :/\: negFormula psi) (- b)

-- primeImplicants :: Formula -> Dir -> System ()
-- primeImplicants phi Zero = primeImplicants (NegAtom phi) One
-- primeImplicants phi One  = undefined

propInvFormulaIncomp :: Formula -> Dir -> Bool
propInvFormulaIncomp phi b = incomparables (invFormula phi b)

prop_invFormula :: Formula -> Dir -> Bool
prop_invFormula phi b =
  all (\alpha -> evalFormula [] phi alpha == Dir b) (invFormula phi b)

testInvFormula :: [Face]
testInvFormula = invFormula (Atom (Name 0) :/\: Atom (Name 1)) 1

-- | Nominal
gensym :: [Name] -> Name
gensym [] = Name 0
gensym xs = Name (max+1)
  where Name max = maximum xs

gensyms :: [Name] -> [Name]
gensyms d = let x = gensym d in x : gensyms (x : d)

class Nominal a where
  support :: a -> [Name]

  occurs :: Name -> a -> Bool
  occurs x v = x `elem` support v

  -- act u (i,phi) should have u # (phi - i) ??
  act     ::  [Name] -> a -> (Name,Formula) -> a

  swap :: a -> (Name,Name) -> a
  -- swap u (i,j) =
  --    where k = fresh (u,i,j)

-- Is used in type checker
fresh :: Nominal a => a -> Name
fresh = gensym . support

freshs :: Nominal a => a -> [Name]
freshs = gensyms . support

unions :: Eq a => [[a]] -> [a]
unions = foldr union []

unionsMap :: Eq b => (a -> [b]) -> [a] -> [b]
unionsMap f = unions . map f

notOccurs :: Nominal a => Name -> a -> Bool
notOccurs x = not . occurs x

instance Nominal () where
  support () = []
  occurs _ () = False
  act _ () _  = ()
  swap () _   = ()

instance (Nominal a, Nominal b) => Nominal (a, b) where
  support (a, b) = support a `union` support b
  occurs x (a,b) = occurs x a || occurs x b
  act s (a,b) f  = (act s a f,act s b f)
  swap (a,b) n   = (swap a n,swap b n)

instance (Nominal a, Nominal b, Nominal c) => Nominal (a, b, c) where
  support (a,b,c)  = unions [support a, support b, support c]
  occurs x (a,b,c) = or [occurs x a,occurs x b,occurs x c]
  act s (a,b,c) f  = (act s a f,act s b f,act s c f)
  swap (a,b,c) n   = (swap a n,swap b n,swap c n)

instance (Nominal a, Nominal b, Nominal c, Nominal d) =>
         Nominal (a, b, c, d) where
  support (a,b,c,d) = unions [support a, support b, support c, support d]
  occurs x (a,b,c,d) = 
    or [occurs x a,occurs x b,occurs x c,occurs x d]
  act s (a,b,c,d) f  = (act s a f,act s b f,act s c f,act s d f)
  swap (a,b,c,d) n   = (swap a n,swap b n,swap c n,swap d n)

instance (Nominal a, Nominal b, Nominal c, Nominal d, Nominal e) =>
         Nominal (a, b, c, d, e) where
  support (a,b,c,d,e)  =
    unions [support a, support b, support c, support d, support e]
  occurs x (a,b,c,d,e) =
    or [occurs x a,occurs x b,occurs x c,occurs x d,occurs x e]
  act s (a,b,c,d,e) f = (act s a f,act s b f,act s c f,act s d f, act s e f)
  swap (a,b,c,d,e) n  =
    (swap a n,swap b n,swap c n,swap d n,swap e n)

instance (Nominal a, Nominal b, Nominal c, Nominal d, Nominal e, Nominal h) =>
         Nominal (a, b, c, d, e, h) where
  support (a,b,c,d,e,h) =
    unions [support a, support b, support c, support d, support e, support h]
  occurs x (a,b,c,d,e,h) =
    or [occurs x a,occurs x b,occurs x c,occurs x d,occurs x e,occurs x h]
  act s (a,b,c,d,e,h) f =
    (act s a f,act s b f,act s c f,act s d f, act s e f, act s h f)
  swap (a,b,c,d,e,h) n  =
    (swap a n,swap b n,swap c n,swap d n,swap e n,swap h n)

instance Nominal a => Nominal [a]  where
  support xs  = unions (map support xs)
  occurs x xs = any (occurs x) xs
  act s xs f  = [ act s x f | x <- xs ]
  swap xs n   = [ swap x n | x <- xs ]

instance Nominal a => Nominal (Maybe a)  where
  support    = maybe [] support
  occurs x   = maybe False (occurs x)
  act s v f  = fmap (\u -> act s u f) v
  swap a n   = fmap (`swap` n) a

instance Nominal Formula where
  support (Dir _)        = []
  support (Atom i)       = [i]
  support (NegAtom i)    = [i]
  support (phi :/\: psi) = support phi `union` support psi
  support (phi :\/: psi) = support phi `union` support psi

  act _ (Dir b) (i,phi)  = Dir b
  act _ (Atom j) (i,phi) | i == j    = phi
                       | otherwise = Atom j
  act _ (NegAtom j) (i,phi) | i == j    = negFormula phi
                          | otherwise = NegAtom j
  act s (psi1 :/\: psi2) (i,phi) = act s psi1 (i,phi) `andFormula` act s psi2 (i,phi)
  act s (psi1 :\/: psi2) (i,phi) = act s psi1 (i,phi) `orFormula` act s psi2 (i,phi)

  swap (Dir b) (i,j)  = Dir b
  swap (Atom k) (i,j)| k == i    = Atom j
                     | k == j    = Atom i
                     | otherwise = Atom k
  swap (NegAtom k) (i,j)| k == i    = NegAtom j
                        | k == j    = NegAtom i
                        | otherwise = NegAtom k
  swap (psi1 :/\: psi2) (i,j) = swap psi1 (i,j) :/\: swap psi2 (i,j)
  swap (psi1 :\/: psi2) (i,j) = swap psi1 (i,j) :\/: swap psi2 (i,j)


face :: Nominal a => [Name] -> a -> Face -> a
face s = Map.foldWithKey (\i d a -> act s a (i,Dir d))

-- the faces should be incomparable
type System a = Map Face a

insertSystem :: Face -> a -> System a -> System a
insertSystem alpha v ts =
  case find (comparable alpha) (Map.keys ts) of
    Just beta | alpha `leq` beta -> ts
              | otherwise        -> Map.insert alpha v (Map.delete beta ts)
    Nothing -> Map.insert alpha v ts

insertsSystem :: [(Face, a)] -> System a -> System a
insertsSystem faces us =
  foldr (\(alpha, ualpha) -> insertSystem alpha ualpha) us faces

mkSystem :: [(Face, a)] -> System a
mkSystem = flip insertsSystem Map.empty

unionSystem :: System a  -> System a  -> System a
unionSystem us vs = insertsSystem (Map.assocs us) vs

-- could something like that work??
-- transposeSystem :: System [a] -> [System a]
-- transposeSystem as = Map.tranverseWithKey (const . id) as

-- TODO: add some checks
transposeSystemAndList :: System [a] -> [b] -> [(System a,b)]
transposeSystemAndList _  []      = []
transposeSystemAndList tss (u:us) =
  (Map.map head tss,u):transposeSystemAndList (Map.map tail tss) us

-- transposeSystem :: System [a] -> [System a]
-- transposeSystem ts =
--   Map.map (\as -> head a) ts : transposeSystem (Map.map (\as -> tail as) ts)

-- Quickcheck this:
-- (i = phi) * beta = (beta - i) * (i = phi beta)

-- Now we ensure that the keys are incomparable
instance Nominal a => Nominal (System a) where
  support s = unions (map Map.keys $ Map.keys s)
              `union` support (Map.elems s)
  occurs x s = x `elem` (concatMap Map.keys $ Map.keys s) || occurs x (Map.elems s)

  act sup s (i, phi) = addAssocs (Map.assocs s)
    where
    addAssocs [] = Map.empty
    addAssocs ((alpha,u):alphaus) =
      let s' = addAssocs alphaus
      in case Map.lookup i alpha of
        -- t'_beta  = t_alpha (delta - i)
        -- where beta = delta gamma
        --   and delta in phi^-1 d
        --   and gamma = alpha - i
        Just d -> foldr (\delta s'' ->
          case meetMaybe delta (Map.delete i alpha) of
            Just beta -> -- TODO: sup is an upper bound; better sup - alpha?
              insertSystem beta (face sup u (Map.delete i delta)) s''
            Nothing    -> s'')
                   s' (invFormula phi d)
        -- t'_alpha = t_alpha (i = phi alpha)
        Nothing -> insertSystem alpha (act sup u (i,face sup phi alpha)) s'

  swap s ij = Map.mapKeys (`swapFace` ij) (Map.map (`swap` ij) s)

-- carve a using the same shape as the system b
border :: Nominal a => [Name] -> a -> System b -> System a
border s v = Map.mapWithKey (const . face s v)

shape :: System a -> System ()
shape ts = border [] () ts

instance (Nominal a, Arbitrary a) => Arbitrary (System a) where
  arbitrary = do
    a  <- arbitrary
    let is = support a
    border is a <$> arbitraryShape is
    where
      arbitraryShape :: [Name] -> Gen (System ())
      arbitraryShape supp = do
        phi <- sized $ arbFormula supp
        return $ Map.fromList [(face,()) | face <- invFormula phi 0]

sym :: Nominal a => [Name] -> a -> Name -> a
sym s a i = act s a (i, NegAtom i)

rename :: Nominal a => [Name] -> a -> (Name, Name) -> a
rename s a (i, j) = act s a (i, Atom j)

connect :: Nominal a => [Name] -> a -> (Name, Name) -> a
connect is a (i, j) = act is a (i, Atom i :/\: Atom j)

leqSystem :: Face -> System a -> Bool
alpha `leqSystem` us =
  not $ Map.null $ Map.filterWithKey (\beta _ -> alpha `leq` beta) us

-- assumes alpha <= shape us
proj :: (Nominal a, Show a) => [Name] -> System a -> Face -> a
proj is us alpha | eps `Map.member` usalpha = usalpha ! eps
                 | otherwise                =
  error $ "proj: eps not in " ++ show usalpha ++ "\nwhich  is the "
    ++ show alpha ++ "\nface of " ++ show us
  where usalpha = face is us alpha

-- actSystemCom :: Formula -> Name -> Formula -> Bool
-- actSystemCom psi i phi = border phi
