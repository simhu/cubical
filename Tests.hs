-- | Unit testing - to run type "runghc Tests".
-- Note: requires that HUnit is installed (cabal update && cabal install HUnit)
module Tests where

import Control.Monad.Error
import Control.Monad.Reader
import Prelude hiding (curry)
import System.Directory
import Test.HUnit

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

-- The folder where the tests are located
folder :: FilePath
folder = "examples/"

lexer :: String -> [Token]
lexer = resolveLayout True . myLexer

imports :: ([String],[String],[Def]) -> String -> IO ([String],[String],[Def])
imports st@(notok,loaded,defs) f
  | f `elem` loaded = return st
  | f `elem` notok  = do
    assertFailure ("Looping imports in" <+> f)
    return ([],[],[])
  | otherwise       = do
    let f' = folder ++ f
    b <- doesFileExist f'
    assertBool ("The file " ++ f' ++ " does not exist") b
    s <- readFile f'
    let ts = lexer s
    case pModule ts of
      Bad err -> do
        assertFailure ("Parse failed:" <+> err <+> "on" <+> f)
        return ([],[],[])
      Ok mod@(Module _ imps defs') -> do
        let imps' = [ unIdent s ++ ".cub" | Import s <- imps ]
        (notok1,loaded1,def1) <- foldM imports (f:notok,loaded,defs) imps'
        return (notok,f:loaded1,def1 ++ defs')

loadFile :: FilePath -> IO C.Env
loadFile f = do
  (_,_,defs) <- imports ([],[],[]) f
  let cs = concat [ [ unIdent n | Sum n _ <- lbls] | DefData _ _ lbls <- defs ]
  case runResolver (local (insertConstrs cs) (resolveDefs defs)) of
    Left err -> do assertFailure $ "Resolver failed:" <+> err <+> "on" <+> f
                   return C.Empty
    Right ds -> TC.runDefs False TC.tEmpty ds >>= \x -> case x of
      Left err    -> do assertFailure $ "Type checking failed:" <+> err <+> "on" <+> f
                        return C.Empty
      Right e -> return (TC.env e)

testFile :: FilePath -> [(String,String)] -> IO ()
testFile f xs = do
  env <- loadFile f
  sequence_ [ do v <- E.evalTer False env (C.Var n)
                 assertEqual ("for" <+> n) output (show v)
            | (n,output) <- xs ]

toTests :: String -> [(String,String)] -> Test
toTests n = TestLabel n . TestCase . testFile (n ++ ".cub")

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

guillaume :: Test
guillaume = toTests "guillaume"
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
tests = TestList [boolEqBool,curry,finite,guillaume,hedberg,nIso,quotient,set,turn]

main :: IO ()
main = void $ runTestTT tests
