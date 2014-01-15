module Tests where

import Control.Monad.Trans.Reader
import Control.Monad.Error
import Data.List
import System.Directory
import System.Environment
import Test.HUnit

import Exp.Lex
import Exp.Par
import Exp.Print
import Exp.Abs hiding (NoArg)
import Exp.Layout
import Exp.ErrM
import Concrete
import Pretty
import qualified MTT as M
import qualified CTT as C
import qualified Eval as E

-- The folder where the tests are located
folder :: FilePath
folder = "examples/"

lexer :: String -> [Token]
lexer = resolveLayout True . myLexer

imports :: ([String],[String],[Def]) -> String -> IO ([String],[String],[Def])
imports st@(notok,loaded,defs) f
  | f `elem` notok  = assertFailure ("Looping imports in" <+> f) >> return ([],[],[])
  | f `elem` loaded = return st
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

testFile :: FilePath -> (String,String) -> IO ()
testFile f test = do
  (_,_,defs) <- imports ([],[],[]) f
  let cs  = concat [ [ unIdent n | Sum n _ <- lbls] | DefData _ _ lbls <- defs ]
  case runResolver (local (insertConstrs cs) (resolveDefs defs)) of
    Left err -> assertFailure $ "Resolver failed:" <+> err <+> "on" <+> f
    Right ds -> case M.runDefs M.tEmpty ds of
      Left err -> assertFailure $ "Type checking failed:" <+> err <+> "on" <+> f
      Right e  -> testStr e test
  where
    -- n, output
    testStr :: M.TEnv -> (String,String) -> IO ()
    testStr (M.TEnv _ rho _) (n,output) =
      assertEqual ("for" <+> n) output (show (E.eval rho (C.Var n)))


toTest :: FilePath -> (String,String) -> Test
toTest fn (n,v) = TestLabel n $ TestCase (testFile fn (n,v))

toTests :: String -> [(String,String)] -> Test
toTests n = TestLabel n . TestList . map (toTest (n ++ ".cub"))

nIso :: Test
nIso = toTests "nIso" [ ("testNO","inl (suc (suc zero))")
                      , ("testNO1","<3> inr tt")
                      , ("testNO2","inr tt")
                      , ("testNO3","inr tt") ]

boolEqBool :: Test
boolEqBool = toTests "BoolEqBool" [ ("testBool","false")
                                  , ("newTestBool","true")
                                  , ("test2Bool","false")
                                  , ("testT"  ,"true")
                                  , ("testT'" ,"true")
                                  , ("testF"  ,"false")
                                  , ("testTT" ,"true")
                                  , ("testTF" ,"true")
                                  , ("testFT" ,"true")
                                  , ("testFF" ,"false")
                                  , ("testTT3","true")
                                  , ("testTF3","true")
                                  , ("testFT3","true")
                                  , ("testFF3","false")
                                  , ("testTT4","<2> true") ]

tests :: Test
tests = TestList [nIso,boolEqBool]

main :: IO ()
main = runTestTT tests >> return ()
