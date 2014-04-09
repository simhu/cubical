-- | Unit testing - to run type "runghc Tests".
-- Note: requires that HUnit is installed (cabal update && cabal install HUnit)
module Tests where

import Control.Monad.Error
import Control.Monad.Reader
import Prelude hiding (curry)
import System.Directory
import Test.HUnit hiding (Label)

import Exp.Lex
import Exp.Par
import Exp.Abs
import Exp.Layout
import Exp.ErrM
import Concrete
import Pretty
import qualified TypeChecker as TC
import qualified CTT as C
import qualified Eval as E
import Main hiding (main)

-- The folder where the tests are located
folder :: FilePath
folder = "examples/"

loadFile :: FilePath -> IO C.OEnv
loadFile f = do
  (_,_,mods) <- imports False ([],[],[]) f
  case runResolver (resolveModules mods) of
    Left err -> do assertFailure $ "Resolver failed:" <+> err <+> "on" <+> f
                   return C.oEmpty
    Right (ds,_) -> TC.runDeclss TC.silentEnv ds >>= \(x , e) -> case x of
      Just err -> do assertFailure $ "Type checking failed:" <+>
                                      err <+> "on" <+> f
                     return (TC.oenv e)
      Nothing  -> return (TC.oenv e)

testFile :: FilePath -> [(String,String)] -> IO ()
testFile f xs = do
  env <- loadFile f
  sequence_ [ do x <- E.evalTer False env (C.Var n)
                 assertEqual ("for" <+> n) output (show x)
            | (n,output) <- xs ]

toTests :: String -> [(String,String)] -> Test
toTests n = TestLabel n . TestCase . testFile (folder ++ n ++ ".cub")

boolEqBool :: Test
boolEqBool = toTests "BoolEqBool" [ ("testBool"   ,"false")
                                  , ("newTestBool","true")
                                  , ("test2Bool"  ,"false")
                                  , ("testT"      ,"true")
                                  , ("testT'"     ,"true")
                                  , ("testF"      ,"false")
                                  , ("testTT"     ,"true")
                                  , ("testTF"     ,"true")
                                  , ("testFT"     ,"true")
                                  , ("testFF"     ,"false")
                                  , ("testTT3"    ,"true")
                                  , ("testTF3"    ,"true")
                                  , ("testFT3"    ,"true")
                                  , ("testFF3"    ,"false")
                                  , ("testTT4"    ,"<2> true") ]

curry :: Test
curry = toTests "curry" [ ("test" ,"zero")
                        , ("test1","suc zero")
                        , ("test2","zero")
                        , ("test4","suc zero")
                        , ("test5","suc zero")
                        , ("test6","suc zero") ]

finite :: Test
finite = toTests "finite" [ ("test" ,"suc zero") ]

heterogeneous :: Test
heterogeneous = toTests "heterogeneous"
  [ ("test","\\A -> \\B -> \\a0 -> \\a1 -> \\b0 -> \\b1 -> " ++
             "\\p -> \\q -> refl (Id A a0 a1) p") ]

hedberg :: Test
hedberg = toTests "hedberg" [ ("test3","<3> <4> zero") ]

nIso :: Test
nIso = toTests "nIso" [ ("testNO" ,"inl (suc (suc zero))")
                      , ("testNO1","<3> inr tt")
                      , ("testNO2","inr tt")
                      , ("testNO3","inr tt") ]


quotient :: Test
quotient = toTests "quotient" [ ("test5","false")
                              , ("test8","true") ]

set :: Test
set = toTests "set" [ ("test2" ,"<3> <4> tt") ]

-- swap :: Test
-- swap = toTests "swap" [ ("test6"  ,"pair true (suc (suc zero))")
--                       , ("test7"  ,"Com U (Box 1 2 Bool [])")
--                      , ("test8"  ,"pair true (suc zero)")
--                       , ("test9"  ,"pair true (suc (suc zero))")
--                       , ("test10" ,"pair true (suc zero)")
--                       , ("test11" ,"pair true (suc (suc zero))")
--                       , ("test12" ,"pair true zero")
--                      , ("test13" ,"Com U (Box 1 2 Bool [])")
--                      , ("test14" ,"pair true (vcomp (Box 1 4 false []))")
--                       , ("test15" ,"true")
--                       , ("test213","zero")
--                       , ("test214","pair true zero")
--                       , ("test215","true") ]

turn :: Test
turn = toTests "turn" [ ("test", "inr (suc (suc zero))")
                      , ("test2", "inr (suc (suc (suc (suc (suc (suc zero))))))")]

tests :: Test
tests = TestList [boolEqBool,curry,finite,heterogeneous,hedberg,nIso,quotient,set,turn]

main :: IO ()
main = void $ runTestTT tests
