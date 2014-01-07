import Data.Char
import Test.QuickCheck


foo p [] = []
foo p (x:xs) = if p x then x:(foo p xs) else foo p xs

isEven :: Int -> Bool
isEven n = if n==0 then True else if n == 1 then False else isEven (n-2)

-- test = quickCheck (\ s -> all isEven (foo isEven s))

-- test = quickCheck ((\ s -> s == s) :: [Char] -> Bool)

bar :: [Int] -> Bool
bar = \ s -> length (take 5 s) <= 4
-- bar s = length (take 5 s) <= 4

-- test = quickCheck bar

double = \ f -> \ x -> f (f x)
-- double f x = f (f x)

test = double (\ x -> x^3) 7
