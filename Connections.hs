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

type Name = String

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

i,j,k,l :: Name
i = "i"
j = "j"
k = "k"
l = "l"

f1,f2 :: Face
f1 = Map.fromList [(i,0),(j,1),(k,0)]
f2 = Map.fromList [(i,0),(j,1),(l,1)]

-- Check if two faces are compatible
compatible :: Face -> Face -> Bool
compatible xs ys = notElem False (Map.elems (Map.intersectionWith (==) xs ys))

compatibles :: [Face] -> Bool
compatibles []     = True
compatibles (x:xs) = all (x `compatible`) xs && compatibles xs

-- Partial composition operation
comp :: Face -> Face -> Face
comp xs ys = Map.unionWith f xs ys
  where f d1 d2 = if d1 == d2 then d1 else error "comp: incompatible faces"

-- TODO: make this primitive?
-- compMaybe :: Face -> Face -> Maybe Face
-- compMaybe x y = if compatible x y then Just $ comp x y else Nothing

compCom :: Face -> Face -> Property
compCom xs ys = compatible xs ys ==> xs `comp` ys == ys `comp` xs

compAssoc :: Face -> Face -> Face -> Property
compAssoc xs ys zs = compatibles [xs,ys,zs] ==>
                     xs `comp` (ys `comp` zs) == (xs `comp` ys) `comp` zs

compId :: Face -> Bool
compId xs = xs `comp` xs == xs

comps :: [Face] -> [Face] -> [Face]
comps xs ys = nub [ comp x y | x <- xs, y <- ys, compatible x y ]

-- instance Ord Face where

-- (<=) :: Face -> Face -> Bool
-- (<=) = undefined

-- Compute the witness of A <= B, ie compute C s.t. B = CA
-- leqW :: Face -> Face -> Face
-- leqW = undefined

-- data Faces = Faces (Set Face)

-- instance Nominal Faces where
--   support (Faces f)      = 
--   act (Faces f) (i, phi) = Faces f

-- | Formulas
data Formula = Dir Dir | Name Name
             | Neg Formula
             | Formula :/\: Formula
             | Formula :\/: Formula
  deriving (Eq,Show)

instance Arbitrary Formula where
  arbitrary = sized arbFormula where
    arbFormula s =
      frequency [ (1, Dir <$> arbitrary)
                , (1, Name <$> elements (map (\x -> 'i' : show x) [0..100]))
                , (s, negFormula <$> arbFormula s')
                , (s, do op <- elements [andFormula,orFormula]
                         op <$> arbFormula s' <*> arbFormula s')
                ]
      where s' = s `div` 2

-- TODO: FINISH!
-- instance Show a => Show (Formula a) where
--   show Zero = "0"
--   show One  = "1"
--   show (Neg a)  = "~" ++ show a
--   show (Name a) = show a
--   show (a :/\: b) = show a ++ " /\ " ++ show b

negFormula :: Formula -> Formula
negFormula (Dir b) = Dir (- b)
negFormula phi     = Neg phi

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
-- evalFormula (Name i) alpha = case Map.lookup i alpha of
--                                Just b -> Dir b
--                                Nothing -> Name i
-- evalFormula (Neg phi) alpha = negFormula (evalFormula phi alpha)
-- evalFormula (phi :/\: psi) alpha =
--   andFormula (evalFormula phi alpha) (evalFormula psi alpha)
-- evalFormula (phi :\/: psi) alpha =
--   orFormula (evalFormula phi alpha) (evalFormula psi alpha)

-- find a better name?
-- phi b = max {alpha : Face | phi alpha = b}
invFormula :: Formula -> Dir -> [Face]
invFormula (Dir b') b          = if b == b' then [Map.empty] else []
invFormula (Name i) b          = [ Map.singleton i b ]
invFormula (Neg phi) b         = invFormula phi (- b)
invFormula (phi :/\: psi) Zero = invFormula phi 0 `union` invFormula psi 0
invFormula (phi :/\: psi) One  =
  comps (invFormula phi 1) (invFormula psi 1)
invFormula (phi :\/: psi) b    = invFormula (Neg phi :/\: Neg psi) (- b)

propInvFormulaIncomp :: Formula -> Dir -> Bool
propInvFormulaIncomp phi b = undefined

prop_invFormula :: Formula -> Dir -> Bool
prop_invFormula phi b =
  all (\alpha -> phi `evalFormula` alpha == Dir b) (invFormula phi b)

testInvFormula :: [Face]
testInvFormula = invFormula (Name j :/\: Name k) 1

-- | Nominal

class Nominal a where
  support :: a -> [Name]
  act     :: a -> (Name,Formula) -> a

-- act u (i,phi) should have u # (phi - i)

unions :: Eq a => [[a]] -> [a]
unions = foldr union []

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
  support (Name i) = [i]
  support (Neg phi)  = support phi
  support (phi :/\: psi) = support phi `union` support psi
  support (phi :\/: psi) = support phi `union` support psi

  act (Dir b) (i,phi) = Dir b
  act (Name j) (i,phi) | i == j = phi
                       | otherwise = Name j
  act (Neg psi) (i,phi) = negFormula (act psi (i,phi))
  act (psi1 :/\: psi2) (i,phi) = act psi1 (i,phi) `andFormula` act psi2 (i,phi)
  act (psi1 :\/: psi2) (i,phi) = act psi1 (i,phi) `orFormula` act psi2 (i,phi)

-- the faces should be incomparable
type System a = Map Face a

instance Nominal a => Nominal (System a) where
  support s = unions (map Map.keys $ Map.keys s)
              `union` support (Map.elems s)

  act s (i, phi) = addKeys (Map.assocs s)
    where
    addKeys [] = Map.empty
    addKeys ((alpha,u):alphaus) =
      let s' = addKeys alphaus
      in case Map.lookup i alpha of
        Just d -> foldr (\beta s'' -> Map.insert beta u s'') s'
                   (invFormula phi d)
        Nothing -> Map.insert alpha (act u (i,phi)) s'

    -- case Map.keys s of
    -- []   -> Map.empty
    -- a:as -> undefined 

-- addSystem :: Nominal a => System a -> Face -> 
