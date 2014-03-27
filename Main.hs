module Main where

import Control.Monad.Trans.Reader
import Control.Monad.Error
import Data.List
import System.Directory
import System.FilePath
import System.Environment
import System.Console.GetOpt
import System.Console.Haskeline

import Exp.Lex
import Exp.Par
import Exp.Print
import Exp.Abs hiding (NoArg)
import Exp.Layout
import Exp.ErrM
import Concrete hiding (getConstrs)
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

-- Used for auto completion
searchFunc :: [String] -> String -> [Completion]
searchFunc ns str = map simpleCompletion $ filter (str `isPrefixOf`) ns

settings :: [String] -> Settings IO
settings ns = Settings
  { historyFile    = Nothing
  , complete       = completeWord Nothing " \t" $ return . searchFunc ns
  , autoAddHistory = True }

main :: IO ()
main = do
  args <- getArgs
  (flags,files) <- parseOpts args
  -- Should it run in debugging mode?
  let b = Debug `elem` flags
  case files of
    [f] -> initLoop b f
    _   -> do putStrLn $ "Exactly one file expected: " ++ show files
              runInputT (settings []) (loop [] [] (TC.verboseEnv b))

-- (not ok,loaded,already loaded defs) -> to load -> (newnotok, newloaded, newdefs)
imports :: ([String],[String],[Module]) -> String ->
  IO ([String],[String],[Module])
imports st@(notok,loaded,mods) f
  | f `elem` notok  = putStrLn ("Looping imports in " ++ f) >> return ([],[],[])
  | f `elem` loaded = return st
  | otherwise       = do
    b      <- doesFileExist f
    let prefix = dropFileName f
    if not b
      then putStrLn (f ++ " does not exist") >> return ([],[],[])
      else do
        s <- readFile f
        let ts = lexer s
        case pModule ts of
          Bad s  -> do
            putStrLn $ "Parse failed in " ++ show f ++ "\n" ++ show s
            return ([],[],[])
          Ok mod@(Module id imp decls) ->
            let name    = unAIdent id
                imp_cub = [prefix ++ unAIdent i ++ ".cub" | Import i <- imp]
            in do
              -- when (name ++ ".cub" /= f) $
              --   error $ "module name mismatch " ++ show (f,name)
              (notok1,loaded1,mods1) <-
                foldM imports (f:notok,loaded,mods) imp_cub
              putStrLn $ "Parsed " ++ show f ++ " successfully!"
              return (notok,f:loaded1,mods1 ++ [mod])

-- getConstrs :: [Decl] -> [String]
-- getConstrs []                  = []
-- getConstrs (DeclData _ _ ls:ds) = [ unAIdent n | Label n _ <- ls] ++ getConstrs ds
-- getConstrs (DeclMutual ds:ds')  = getConstrs ds ++ getConstrs ds'
-- getConstrs (_:ds)              = getConstrs ds

namesEnv :: TC.TEnv -> [String]
namesEnv (TC.TEnv _ env ctxt _ _) = namesCEnv env ++ [n | ((n,_),_) <- ctxt]
  where namesCEnv C.Empty              = []
        namesCEnv (C.Pair e ((x,_),_)) = namesCEnv e ++ [x]
        namesCEnv (C.PDef xs e)        =  [n | ((n,_),_) <- ctxt] ++ namesCEnv e

-- Initialize the main loop
initLoop :: Bool -> FilePath -> IO ()
initLoop debug f = do
  -- Parse and type-check files
  (_,_,mods) <- imports ([],[],[]) f
  -- Translate to CTT
  let res = runResolver $ resolveModules mods
  -- putStrLn $ show res
  case res of
    Left err    -> do
      putStrLn $ "Resolver failed: " ++ err
      runInputT (settings []) (loop [] [] (TC.verboseEnv debug))
    Right (adefs,names) -> do
      (merr , tenv) <- TC.runDeclss (TC.verboseEnv debug) adefs
      case merr of
        Just err -> putStrLn $ "Type checking failed: " ++ err
        Nothing  -> return ()
      putStrLn "File loaded."
      -- Compute names for auto completion
      runInputT (settings [n | ((n,_),_) <- names]) (loop f names tenv)

-- The main loop
loop :: FilePath -> [(C.Binder,Bool)] -> TC.TEnv -> Interpreter ()
loop f names tenv@(TC.TEnv _ rho _ _ debug) = do
  input <- getInputLine defaultPrompt
  case input of
    Nothing    -> outputStrLn help >> loop f names tenv
    Just ":q"  -> return ()
    Just ":r"  -> lift $ initLoop debug f
    Just (':':'l':' ':str)
      | ' ' `elem` str -> do outputStrLn "Only one file allowed after :l"
                             loop f names tenv
      | otherwise      -> lift $ initLoop debug str
    Just (':':'c':'d':' ':str) -> do lift (setCurrentDirectory str)
                                     loop f names tenv
    Just ":h"  -> outputStrLn help >> loop f names tenv
    Just str   -> case pExp (lexer str) of
      Bad err -> outputStrLn ("Parse error: " ++ err) >> loop f names tenv
      Ok  exp ->
        case runResolver $ local (insertBinders names) $ resolveExp exp of
          Left  err  -> do outputStrLn ("Resolver failed: " ++ err)
                           loop f names tenv
          Right body -> do
          x <- liftIO $ TC.runInfer tenv body
          case x of
            Left err -> do outputStrLn ("Could not type-check: " ++ err)
                           loop f names tenv
            Right _  -> do
              let e = E.evalTer debug rho body
              outputStrLn ("EVAL: " ++ show e)
              loop f names tenv

help :: String
help = "\nAvailable commands:\n" ++
       "  <statement>     infer type and evaluate statement\n" ++
       "  :q              quit\n" ++
       "  :l <filename>   loads filename (and resets environment before)\n" ++
       "  :cd <path>      change directory to path\n" ++
       "  :r              reload\n" ++
       "  :h              display this message\n"
