-- Common functions used for pretty printing.
module Pretty where

--------------------------------------------------------------------------------
-- | Pretty printing combinators. Use the same names as in the pretty library.

(<+>) :: String -> String -> String
[] <+> y  = y
x  <+> [] = x
x  <+> y  = x ++ " " ++ y

infixl 6 <+>

hcat :: [String] -> String
hcat []     = []
hcat [x]    = x
hcat (x:xs) = x <+> hcat xs

ccat :: [String] -> String
ccat []     = []
ccat [x]    = x
ccat (x:xs) = x <+> "," <+> ccat xs

parens :: String -> String
parens [] = ""
parens p  = "(" ++ p ++ ")"

brackets :: String -> String
brackets p  = "[ " ++ p ++ " ]"

-- Angled brackets, not present in pretty library.
abrack :: String -> String
abrack [] = ""
abrack p  = "<" ++ p ++ ">"
