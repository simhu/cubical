module Main where

import Control.Monad.Trans.Reader
import Control.Monad.Error
import Data.List
import System.Directory
import System.Environment
import System.Console.GetOpt
import System.Console.Haskeline

import Exp.Lex
import Exp.Par
import Exp.Print
import Exp.Abs hiding (NoArg)
import Exp.Layout
import Exp.ErrM
import Concrete
import qualified TypeChecker as TC
import qualified CTT as C
import qualified Eval as E

type Interpreter a = InputT IO a

-- Flag handling
data Flag = Debug
  deriving (Eq,Show)

options :: [OptDescr Flag]
options = [ Option "d" ["debug"] (NoArg Debug) "Run in debugging mode" ]

parseOpts :: [String] -> IO ([Flag],[String])
parseOpts argv = case getOpt Permute options argv of
  (o,n,[])   -> return (o,n)
  (_,_,errs) -> ioError (userError (concat errs ++ usageInfo header options))
    where header = "Usage: cubical [OPTION...] [FILES...]"

defaultPrompt :: String
defaultPrompt = "> "

lexer :: String -> [Token]
lexer = resolveLayout True . myLexer

showTree :: (Show a, Print a) => a -> IO ()
showTree tree = do
  putStrLn $ "\n[Abstract Syntax]\n\n" ++ show tree
  putStrLn $ "\n[Linearized tree]\n\n" ++ printTree tree

main :: IO ()
main = do
  args <- getArgs
  (flags,files) <- parseOpts args
  runInputT defaultSettings $ runInterpreter (Debug `elem` flags) files

-- (not ok,loaded,already loaded defs) -> to load -> (newnotok, newloaded, newdefs)
imports :: ([String],[String],[Def]) -> String -> Interpreter ([String],[String],[Def])
imports st@(notok,loaded,defs) f
  | f `elem` notok  = do
    outputStrLn $ "Looping imports in " ++ f
    return ([],[],[])
  | f `elem` loaded = return st
  | otherwise       = do
    b <- lift $ doesFileExist f
    if not b
      then do
        outputStrLn ("The file " ++ f ++ " does not exist")
        return ([],[],[])
      else do
        s <- lift $ readFile f
        let ts = lexer s
        case pModule ts of
          Bad s  -> do
            outputStrLn $ "Parse Failed in file " ++ show f ++ "\n" ++ show s
            return ([],[],[])
          Ok mod@(Module _ imps defs') -> do
            let imps' = [ unIdent s ++ ".cub" | Import s <- imps ]
            (notok1,loaded1,def1) <- foldM imports (f:notok,loaded,defs) imps'
            outputStrLn $ "Parsed file " ++ show f ++ " successfully!"
            return (notok,f:loaded1,def1 ++ defs')

-- defs :: C.Env -> C.Ter -> C.Ter
-- defs C.Empty        t = t
-- defs (C.PDef d env) t = defs env (C.Where t d)
-- defs env          _ =
--   error $ "defs: environment should a list of definitions " ++ show env

getConstructors :: [Def] -> [String]
getConstructors [] = []
getConstructors (DefData _ _ lbls:defs) =
  [ unIdent n | Sum n _ <- lbls] ++ getConstructors defs
getConstructors (DefMutual ds:ds') = getConstructors ds ++ getConstructors ds'
getConstructors (_:ds) = getConstructors ds

-- The Bool is intended to be whether or not to run in debug mode
runInterpreter :: Bool -> [FilePath] -> Interpreter ()
runInterpreter b fs = case fs of
  [f] -> do
    -- parse and type-check files
    (_,_,defs) <- imports ([],[],[]) f
    -- Compute all constructors
    let cs = getConstructors defs
    let res = runResolver (local (insertConstrs cs) (resolveDefs defs))
    case res of
      Left err    -> do
        outputStrLn $ "Resolver failed: " ++ err
        loop [] TC.tEmpty
      Right adefs -> case TC.runDefs TC.tEmpty adefs of
        Left err   -> do
          outputStrLn $ "Type checking failed: " ++ err
          loop [] TC.tEmpty
        Right tenv -> do
          outputStrLn "File loaded."
          loop cs tenv
  _   -> do
    outputStrLn $ "Exactly one file expected: " ++ show fs
    loop [] TC.tEmpty
  where
    loop :: [String] -> TC.TEnv -> Interpreter ()
    loop cs tenv@(TC.TEnv _ rho _) = do
      input <- getInputLine defaultPrompt
      case input of
        Nothing    -> outputStrLn help >> loop cs tenv
        Just ":q"  -> return ()
        Just ":r"  -> runInterpreter b fs
        Just (':':'l':' ':str) -> runInterpreter b (words str)
        Just (':':'c':'d':' ':str) -> lift (setCurrentDirectory str) >> loop cs tenv
        Just ":h"  -> outputStrLn help >> loop cs tenv
        Just str   -> let ts = lexer str in
          case pExp ts of
            Bad err -> outputStrLn ("Parse error: " ++ err) >> loop cs tenv
            Ok exp  ->
              case runResolver (local (const (Env cs)) (resolveExp exp)) of
                Left err   -> outputStrLn ("Resolver failed: " ++ err) >> loop cs tenv
                Right body ->
                  case TC.runInfer tenv body of
                    Left err -> outputStrLn ("Could not type-check: " ++ err) >> loop cs tenv
                    Right _  ->
                      let value = E.eval rho body
                          -- t = defs rho body
                          -- value = E.eval C.Empty t
                      in outputStrLn ("EVAL: " ++ show value) >> loop cs tenv

help :: String
help = "\nAvailable commands:\n" ++
       "  <statement>     infer type and evaluate statement\n" ++
       "  :q              quit\n" ++
       "  :l <filename>   loads filename (and resets environment before)\n" ++
       "  :cd <path>      change directory to path\n" ++
       "  :r              reload\n" ++
       "  :h              display this message\n"
