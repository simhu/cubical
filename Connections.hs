{-# LANGUAGE TypeSynonymInstances, FlexibleInstances #-}
module Connections where

import Control.Applicative
import Data.List
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe
import Test.QuickCheck

type Name = Char

data Dir  = Zero | One
  deriving (Eq,Ord)

instance Show Dir where
  show Zero = "0"
  show One  = "1"

instance Num Dir where
  Zero + x = x
  x + Zero = x
  One + One = Zero

  Zero * _ = Zero
  _ * Zero = Zero
  One * x  = x
  
  abs    = id
  signum = id -- ?
  negate = id

  fromInteger 0 = Zero
  fromInteger 1 = One
  fromInteger _ = error "fromInteger Dir"

instance Arbitrary Dir where
  arbitrary = do
    b <- arbitrary
    return $ if b then Zero else One

-- Formulas
data Formula = Dir Dir | Neg Name | Name Name
             | Formula :/\: Formula
             | Formula :\/: Formula
  deriving (Eq,Show)

-- TODO: FINISH!
-- instance Show a => Show (Formula a) where
--   show Zero = "0"
--   show One  = "1"
--   show (Neg a)  = "~" ++ show a
--   show (Name a) = show a
--   show (a :/\: b) = show a ++ " /\ " ++ show b

-- TODO: Push negations in. Don't distribute.
-- reduce :: Formula a -> Formula a
-- reduce = undefined

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

-- Faces of the form: [(i,0),(j,1),(k,0)]
type Face = Map Name Dir

instance Arbitrary Face where
  arbitrary = Map.fromList <$> arbitrary

i,j,k,l :: Name
i = 'i'
j = 'j'
k = 'k'
l = 'l'

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
  where f d1 d2 = if d1 == d2 then d1 else error "comp: Not compatible faces"

compCom :: Face -> Face -> Property
compCom xs ys = compatible xs ys ==> xs `comp` ys == ys `comp` xs

compAssoc :: Face -> Face -> Face -> Property
compAssoc xs ys zs = compatibles [xs,ys,zs] ==>
                     xs `comp` (ys `comp` zs) == (xs `comp` ys) `comp` zs

-- Faces of the form: [(i,0),(j,1),(k,0)]
-- Should be sorted wrt Name
-- type Face = [(Name,Dir)]

-- -- Check if two faces are compatible
-- compatible :: Face -> Face -> Bool
-- compatible [] _ = True
-- compatible _ [] = True
-- compatible ((i,di):is) ((j,dj):js) | i == j = di == dj && compatible is js
--                                    | i < j  = compatible is ((j,dj):js)
--                                    | i > j  = compatible ((i,di):is) js

-- compatibles :: [Face] -> Bool
-- compatibles [] = True
-- compatibles (x:xs) = all (x `compatible`) xs && compatibles xs 

-- -- Partial composition operation
-- comp :: Face -> Face -> Face
-- comp [] ys = ys
-- comp xs [] = xs
-- comp xs@((i,di):is) ys@((j,dj):js)
--   | i == j && di == dj = (i,di) : comp is js
--   | i < j              = (i,di) : comp is ys
--   | i > j              = (j,dj) : comp xs js
--   | otherwise = error $ "comp: Not compatible input " ++ show xs ++ " " ++ show ys
                                       
-- sorted :: Ord a => [a] -> Bool
-- sorted xs = sort xs == xs

-- -- TODO: Generate only sorted faces
-- compSorted :: Face -> Face -> Property
-- compSorted xs ys = sorted xs && sorted ys ==> sorted (xs `comp` ys)

-- compCom :: Face -> Face -> Property
-- compCom xs ys = compatible xs ys ==> xs `comp` ys == ys `comp` xs

-- compAssoc :: Face -> Face -> Face -> Property
-- compAssoc xs ys zs = compatibles [xs,ys,zs] ==>
--                      xs `comp` (ys `comp` zs) == (xs `comp` ys) `comp` zs

-- compId :: Face -> Bool
-- compId xs = xs `comp` xs == xs

-- (<=) :: Face -> Face -> Bool
-- (<=) = undefined

-- -- Compute the witness of A <= B, ie compute C s.t. B = CA
-- leqW :: Face -> Face -> Face
-- leqW = undefined

-- -- L-Systems:

-- -- TEMP
-- type Val = ()

-- type System = [(Face,Val)]

-- instance Nominal System where
--   support = undefined
--   act = undefined
