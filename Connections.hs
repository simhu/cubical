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
  signum _ = One

  negate Zero = One
  negate One = Zero

  fromInteger 0 = Zero
  fromInteger 1 = One
  fromInteger _ = error "fromInteger Dir"

orDir :: Dir -> Dir -> Dir
orDir Zero Zero = Zero
orDir _ _       = One

instance Arbitrary Dir where
  arbitrary = do
    b <- arbitrary
    return $ if b then Zero else One

-- Formulas
data Formula = Dir Dir | Name Name
             | Neg Formula 
             | Formula :/\: Formula
             | Formula :\/: Formula
  deriving (Eq,Show)

instance Arbitrary Formula where
  arbitrary = sized gen_of where
    gen_of 0 = oneof [fmap Dir arbitrary, fmap Name arbitrary]
    gen_of n = frequency [(1, Neg <$> (gen_of (n - 1)))
                         ,(2, do con <- elements [(:/\:), (:\/:)]
                                 con <$> gen_of (n - 1) <*> gen_of (n - 1))]


--  [genNeg, genAndOr True, genAndOr False]

--     genNeg 
    
-- do
--       i <- elements [0,1,2]
--       phi <- gen_of (n - 1)
--       if i == 0 then return (Neg phi)
--       else do psi <- gen_of (n - 1)
--               return $ (if i == 1 then (:/\:) else (:\/:)) phi psi

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
  where f d1 d2 = if d1 == d2 then d1 else error "comp: incompatible faces"

-- TODO: make this primitive?
-- compMaybe :: Face -> Face -> Maybe Face
-- compMaybe x y = if compatible x y then Just $ comp x y else Nothing

compCom :: Face -> Face -> Property
compCom xs ys = compatible xs ys ==> xs `comp` ys == ys `comp` xs

compAssoc :: Face -> Face -> Face -> Property
compAssoc xs ys zs = compatibles [xs,ys,zs] ==>
                     xs `comp` (ys `comp` zs) == (xs `comp` ys) `comp` zs

-- data Faces = Faces (Set Face)

-- instance Nominal Faces where
--   support (Faces f)      = 
--   act (Faces f) (i, phi) = Faces f

comps :: [Face] -> [Face] -> [Face]
comps xs ys = [comp x y | x <- xs, y <- ys, compatible x y]

negFormula :: Formula -> Formula
negFormula (Dir b) = Dir (- b)
negFormula phi     = Neg phi

andFormula :: Formula -> Formula -> Formula
andFormula (Dir b) (Dir b') = Dir $ b * b'
andFormula phi psi          = phi :/\: psi

orFormula :: Formula -> Formula -> Formula
orFormula (Dir b) (Dir b') = Dir $ b `orDir` b'
orFormula phi psi          = phi :\/: psi

evalFormula :: Formula -> Face -> Formula
evalFormula (Dir b) alpha  = Dir b
evalFormula (Name i) alpha = case Map.lookup i alpha of
                               Just b -> Dir b
                               Nothing -> Name i
evalFormula (Neg phi) alpha = negFormula (evalFormula phi alpha)
evalFormula (phi :/\: psi) alpha =
  andFormula (evalFormula phi alpha) (evalFormula psi alpha)
evalFormula (phi :\/: psi) alpha =
  orFormula (evalFormula phi alpha) (evalFormula psi alpha)

-- find a better name?
-- phi b = max {alpha : Face | phi alpha = b}
orthFaces :: Formula -> Dir -> [Face]
orthFaces (Dir b') b = if b == b' then [Map.empty] else []
orthFaces (Name i) b = [Map.fromList [(i, b)]]
orthFaces (Neg phi) b = orthFaces phi (- b)
orthFaces (phi :/\: psi) Zero = nub (orthFaces phi Zero ++ orthFaces psi Zero)
orthFaces (phi :/\: psi) One = nub $ comps (orthFaces phi One) (orthFaces psi One)
orthFaces (phi :\/: psi) b = orthFaces (Neg phi :/\: Neg psi) (- b)

orthFacesProp :: Face -> Formula -> Dir -> Bool
orthFacesProp alpha phi b =
 all (\alpha -> phi `evalFormula` alpha == Dir b) (orthFaces phi b)

-- the faces should be incomparable
type System a = Map Face a

instance Nominal a => Nominal (System a) where
  support s = unions (map Map.keys $ Map.keys s) 
              `union` support (Map.elems s)

  act s (i, phi) = s

           



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
