{-# LANGUAGE TypeSynonymInstances, FlexibleInstances #-}
module Connections where

import Control.Applicative
import Data.List
import Data.Map (Map)
import Data.Set (Set)
import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.Maybe
import Test.QuickCheck

newtype Name = Name Integer
  deriving (Eq,Ord)

instance Show Name where
    show (Name i) = "i" ++ show i

instance Arbitrary Name where
    arbitrary = Name <$> arbitrary

-- | Directions
data Dir  = Zero | One
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
compatible xs ys = notElem False (Map.elems (Map.intersectionWith (==) xs ys))

compatibles :: [Face] -> Bool
compatibles []     = True
compatibles (x:xs) = all (x `compatible`) xs && compatibles xs

-- Partial composition operation
join :: Face -> Face -> Face
join xs ys = Map.unionWith f xs ys
  where f d1 d2 = if d1 == d2 then d1 else error "join: incompatible faces"

-- TODO: make this primitive?
-- joinMaybe :: Face -> Face -> Maybe Face
-- joinMaybe x y = if compatible x y then Just $ join x y else Nothing

joinCom :: Face -> Face -> Property
joinCom xs ys = compatible xs ys ==> xs `join` ys == ys `join` xs

joinAssoc :: Face -> Face -> Face -> Property
joinAssoc xs ys zs = compatibles [xs,ys,zs] ==>
                     xs `join` (ys `join` zs) == (xs `join` ys) `join` zs

joinId :: Face -> Bool
joinId xs = xs `join` xs == xs

joins :: [Face] -> [Face] -> [Face]
joins xs ys = nub [ join x y | x <- xs, y <- ys, compatible x y ]

-- instance Ord Face where

leq :: Face -> Face -> Bool
alpha `leq` beta | compatible alpha beta = join alpha beta == alpha
                 | otherwise             = False

incomparable :: Face -> Face -> Bool
incomparable alpha beta = not (alpha `leq` beta || beta `leq` alpha)

incomparables :: [Face] -> Bool
incomparables []     = True
incomparables (x:xs) = all (x `incomparable`) xs && incomparables xs

-- Compute the witness of A <= B, ie compute C s.t. B = CA
-- leqW :: Face -> Face -> Face
-- leqW = undefined

-- data Faces = Faces (Set Face)

-- instance Nominal Faces where
--   support (Faces f)      = 
--   act (Faces f) (i, phi) = Faces f

-- | Formulas
data Formula = Dir Dir | Atom Name
             | Not Formula
             | Formula :/\: Formula
             | Formula :\/: Formula
  deriving (Eq,Show)

arbFormula :: [Name] -> Int -> Gen Formula
arbFormula names s =
      frequency [ (1, Dir <$> arbitrary)
                , (1, Atom <$> elements names)
                , (s, notFormula <$> arbFormula names s')
                , (s, do op <- elements [andFormula,orFormula]
                         op <$> arbFormula names s' <*> arbFormula names s')
                ]
      where s' = s `div` 2

instance Arbitrary Formula where
  arbitrary = do
      n <- arbitrary :: Gen Integer
      sized $ arbFormula (map Name [0..n])


-- TODO: FINISH!
-- instance Show a => Show (Formula a) where
--   show Zero = "0"
--   show One  = "1"
--   show (Not a)  = "~" ++ show a
--   show (Atom a) = show a
--   show (a :/\: b) = show a ++ " /\ " ++ show b

notFormula :: Formula -> Formula
notFormula (Dir b) = Dir (- b)
notFormula phi     = Not phi

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

evalFormula :: Formula -> Face -> Formula
evalFormula phi alpha =
  Map.foldWithKey (\i d psi -> act psi (i,Dir d)) phi alpha 

  -- (Dir b) alpha  = Dir b
-- evalFormula (Atom i) alpha = case Map.lookup i alpha of
--                                Just b -> Dir b
--                                Nothing -> Atom i
-- evalFormula (Not phi) alpha = notFormula (evalFormula phi alpha)
-- evalFormula (phi :/\: psi) alpha =
--   andFormula (evalFormula phi alpha) (evalFormula psi alpha)
-- evalFormula (phi :\/: psi) alpha =
--   orFormula (evalFormula phi alpha) (evalFormula psi alpha)

-- find a better name?
-- phi b = max {alpha : Face | phi alpha = b}
invFormula :: Formula -> Dir -> [Face]
invFormula (Dir b') b          = if b == b' then [Map.empty] else []
invFormula (Atom i) b          = [ Map.singleton i b ]
invFormula (Not phi) b         = invFormula phi (- b)
invFormula (phi :/\: psi) Zero = invFormula phi 0 `union` invFormula psi 0
invFormula (phi :/\: psi) One  =
  joins (invFormula phi 1) (invFormula psi 1)
invFormula (phi :\/: psi) b    = invFormula (Not phi :/\: Not psi) (- b)

propInvFormulaIncomp :: Formula -> Dir -> Bool
propInvFormulaIncomp phi b = incomparables (invFormula phi b)

prop_invFormula :: Formula -> Dir -> Bool
prop_invFormula phi b =
  all (\alpha -> phi `evalFormula` alpha == Dir b) (invFormula phi b)

testInvFormula :: [Face]
testInvFormula = invFormula (Atom (Name 0) :/\: Atom (Name 1)) 1

-- | Nominal
gensym :: [Name] -> Name
gensym [] = Name 0
gensym xs = Name $ maximum (map (\(Name n) -> n) xs) + 1

gensyms :: [Name] -> [Name]
gensyms d = let x = gensym d in x : gensyms (x : d)

class Nominal a where
  support :: a -> [Name]
-- act u (i,phi) should have u # (phi - i) ??
  act     :: a -> (Name,Formula) -> a

fresh :: Nominal a => a -> Name
fresh = gensym . support

freshs :: Nominal a => a -> [Name]
freshs = gensyms . support

unions :: Eq a => [[a]] -> [a]
unions = foldr union []

unionsMap :: Eq b => (a -> [b]) -> [a] -> [b]
unionsMap f = unions . map f

instance Nominal () where
  support () = []
  act () _   = ()

instance (Nominal a, Nominal b) => Nominal (a, b) where
  support (a, b)  = support a `union` support b
  act (a,b) f = (act a f,act b f)

instance Nominal a => Nominal [a]  where
  support xs  = unions (map support xs)
  act xs f    = [ act x f | x <- xs ]

instance Nominal a => Nominal (Maybe a)  where
  support = maybe [] support
  act v f = fmap (\u -> act u f) v

instance Nominal Formula where
  support (Dir _) = []
  support (Atom i) = [i]
  support (Not phi)  = support phi
  support (phi :/\: psi) = support phi `union` support psi
  support (phi :\/: psi) = support phi `union` support psi

  act (Dir b) (i,phi) = Dir b
  act (Atom j) (i,phi) | i == j = phi
                       | otherwise = Atom j
  act (Not psi) (i,phi) = notFormula (act psi (i,phi))
  act (psi1 :/\: psi2) (i,phi) = act psi1 (i,phi) `andFormula` act psi2 (i,phi)
  act (psi1 :\/: psi2) (i,phi) = act psi1 (i,phi) `orFormula` act psi2 (i,phi)

face :: Nominal a => a -> Face -> a
face = Map.foldWithKey (\i d a -> act a (i,Dir d))

-- the faces should be incomparable
type System a = Map Face a

-- Quickcheck this:
-- (i = phi) * beta = (beta - i) * (i = phi beta)

instance Nominal a => Nominal (System a) where
  support s = unions (map Map.keys $ Map.keys s)
              `union` support (Map.elems s)

  act s (i, phi) = addAssocs (Map.assocs s)
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
                             Map.insert (join delta (Map.delete i alpha))
                                        (face u (Map.delete i delta)) s'')
                  s' (invFormula phi d)
        -- t'_alpha = t_alpha (i = phi alpha)
        Nothing -> Map.insert alpha (act u (i,face phi alpha)) s'

-- carve a using the same shape as the system b
border :: Nominal a => a -> System b -> System a
border v = Map.mapWithKey (const . face v)

instance (Nominal a, Arbitrary a) => Arbitrary (System a) where
  arbitrary = do
    a <- arbitrary
    border a <$> arbitraryShape (support a)
    where
      arbitraryShape :: [Name] -> Gen (System ())
      arbitraryShape supp = do
        phi <- sized $ arbFormula supp
        return $ Map.fromList [(face,()) | face <- invFormula phi 0]

sym :: Nominal a => a -> Name -> a
sym a i = a `act` (i, Not $ Atom i)

rename :: Nominal a => a -> (Name, Name) -> a
rename a (i, j) = a `act` (i, Atom j)

connect :: Nominal a => a -> (Name, Name) -> a
connect a (i, j) = a `act` (i, Atom i :/\: Atom j)

-- actSystemCom :: Formula -> Name -> Formula -> Bool
-- actSystemCom psi i phi = border phi


