module Main where

import Control.Monad.Trans.Reader
import Control.Monad.Error
import Data.List
import Data.Time
import System.Directory
import System.FilePath
import System.Environment
import System.Console.GetOpt
import System.Console.Haskeline
import Text.Printf

import Exp.Lex
import Exp.Par
import Exp.Print
import Exp.Abs
import Exp.Layout
import Exp.ErrM
import Concrete
import qualified TypeChecker as TC
import qualified CTT as C
import qualified Eval as E

type Interpreter a = InputT IO a

-- Flag handling
data Flag = Help | Version | Time
  deriving (Eq,Show)

options :: [OptDescr Flag]
options = [ Option ""    ["help"]    (NoArg Help)    "print help"
          , Option "-t"  ["time"]    (NoArg Time)    "measure time spent computing"
          , Option ""    ["version"] (NoArg Version) "print version number" ]

-- Version number, welcome message, usage and prompt strings
version, welcome, usage, prompt :: String
version = "0.2.0"
welcome = "cubical, version: " ++ version ++ "  (:h for help)\n"
usage   = "Usage: cubical [options] <file.cub>\nOptions:"
prompt  = "> "

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
  case getOpt Permute options args of
    (flags,files,[])
      | Help    `elem` flags -> putStrLn $ usageInfo usage options
      | Version `elem` flags -> putStrLn version
      | otherwise -> case files of
       []  -> do
         putStrLn welcome
         runInputT (settings []) (loop flags [] [] TC.verboseEnv)
       [f] -> do
         putStrLn welcome
         putStrLn $ "Loading " ++ show f
         initLoop flags f
       _   -> putStrLn $ "Input error: zero or one file expected\n\n" ++
                         usageInfo usage options
    (_,_,errs) -> putStrLn $ "Input error: " ++ concat errs ++ "\n" ++
                             usageInfo usage options

-- Initialize the main loop
initLoop :: [Flag] -> FilePath -> IO ()
initLoop flags f = do
  -- Parse and type-check files
  (_,_,mods) <- imports True ([],[],[]) f
  -- Translate to CTT
  let res = runResolver $ resolveModules mods
  case res of
    Left err    -> do
      putStrLn $ "Resolver failed: " ++ err
      runInputT (settings []) (loop flags f [] TC.verboseEnv)
    Right (adefs,names) -> do
      (merr,tenv) <- TC.runDeclss TC.verboseEnv [adef | C.ODecls adef <- adefs]
      case merr of
        Just err -> putStrLn $ "Type checking failed: " ++ err
        Nothing  -> putStrLn "File loaded."
      -- Compute names for auto completion
      runInputT (settings [n | ((n,_),_) <- names]) (loop flags f names tenv)

      -- l <- getLine

      -- truncS2:
      -- test "test" names tenv
      -- test "test1" names tenv
      -- test "test2" names tenv

      -- pi1S2:
      -- test "test" names tenv   -- Time: 8m34.017s
      -- test "test1" names tenv  -- Time: 4m45.517s
      -- test "test2" names tenv  -- Time: 4m49.252s
      -- test "test3" names tenv  -- Crashes!
      -- test "test4" names tenv     -- Time: 0m31.528s
      -- test "test5" names tenv     -- Time: 0m31.703s

      -- pi4s3:
      -- Works:
      -- test "test0To1" names tenv
      -- test "test0To2" names tenv
      -- test "test0To3" names tenv
      -- test "test0To4" names tenv
      -- test "testShortcut2To9" names tenv
      -- -- test "testShortcut3To6" names tenv
      -- test "testShortcut2To8" names tenv
      -- test "testShortcut2To7" names tenv
      -- test "fast" names tenv

      -- Don't work:
      -- test "test0To5" names tenv
      -- test "test0To6" names tenv
      -- test "test0To7" names tenv
      -- test "testShortcut4To5" names tenv
      -- test "slow" names tenv
      -- test "genPi3S2" names tenv
      -- test "testf5" names tenv
      -- getLine >>= \input -> test input names tenv
      -- runInputT (settings [n | ((n,_),_) <- names]) (loop flags f names tenv)
      -- test "test2" names tenv
      
test str names tenv@(TC.TEnv _ rho _ _) = do
  putStrLn str
  case pExp (lexer str) of
        Bad err -> do putStrLn ("Parse error: " ++ err)
                      -- loop flags f names tenv
        Ok  exp ->
          case runResolver $ local (insertBinders names) $ resolveExp exp of
            Left  err  -> do putStrLn ("Resolver failed: " ++ err)
                             -- loop flags f names tenv
            Right body -> do
              x <- liftIO $ TC.runInfer tenv body
              case x of
                Left err -> do putStrLn ("Could not type-check: " ++ err)
                               -- loop flags f names tenv
                Right _  -> do
                  start <- liftIO getCurrentTime
                  let e = E.eval [] rho body
                  -- putStrLn ("EVAL: " ++ show (length (show e)))
                  putStrLn ("EVAL: " ++ show e)
                  stop <- liftIO getCurrentTime
                  let time = diffUTCTime stop start
                      secs = read (takeWhile (/='.') (init (show time)))
                      rest = read ('0':dropWhile (/='.') (init (show time)))
                      mins = secs `quot` 60
                      sec  = printf "%.3f" (fromInteger (secs `rem` 60) + rest :: Float)
                  putStrLn $ "Time: " ++ show mins ++ "m" ++ sec ++ "s"


              -- let e = E.eval [] rho body
              --     putStrLn ("EVAL: " ++ show (length (show e)))


-- The main loop
loop :: [Flag] -> FilePath -> [(C.Binder,SymKind)] -> TC.TEnv -> Interpreter ()
loop flags f names tenv@(TC.TEnv _ rho _ _) = do
  input <- getInputLine prompt
  case input of
    Nothing    -> outputStrLn help >> loop flags f names tenv
    Just ":q"  -> return ()
    Just ":r"  -> lift $ initLoop flags f
    Just (':':'l':' ':str)
      | ' ' `elem` str -> do outputStrLn "Only one file allowed after :l"
                             loop flags f names tenv
      | otherwise      -> lift $ initLoop flags str
    Just (':':'c':'d':' ':str) -> do lift (setCurrentDirectory str)
                                     loop flags f names tenv
    Just ":h"  -> outputStrLn help >> loop flags f names tenv
    -- Just (':':'n':' ':str) ->
    --   case pExp (lexer str) of
    --   Bad err -> outputStrLn ("Parse error: " ++ err) >> loop flags f names tenv
    --   Ok  exp ->
    --     case runResolver $ local (insertBinders names) $ resolveExp exp of
    --       Left  err  -> do outputStrLn ("Resolver failed: " ++ err)
    --                        loop flags f names tenv
    --       Right body -> do
    --       x <- liftIO $ TC.runInfer tenv body
    --       case x of
    --         Left err -> do outputStrLn ("Could not type-check: " ++ err)
    --                        loop flags f names tenv
    --         Right _  -> do
    --           let e = E.normal 0 (E.eval rho body)
    --           outputStrLn ("NORMEVAL: " ++ show e)
    --           loop flags f names tenv
    Just str' ->
      let (msg,str,mod) = case str' of
            -- (':':'n':' ':str) ->
            --   ("NORMEVAL: ",str,E.normal 0 :: C.Val->C.Val)
            str -> ("EVAL: ",str,id)
      in case pExp (lexer str) of
        Bad err -> do outputStrLn ("Parse error: " ++ err)
                      loop flags f names tenv
        Ok  exp ->
          case runResolver $ local (insertBinders names) $ resolveExp exp of
            Left  err  -> do outputStrLn ("Resolver failed: " ++ err)
                             loop flags f names tenv
            Right body -> do
              x <- liftIO $ TC.runInfer tenv body
              case x of
                Left err -> do outputStrLn ("Could not type-check: " ++ err)
                               loop flags f names tenv
                Right _  -> do
                  start <- liftIO getCurrentTime
                  let e = E.eval [] rho body
                  outputStrLn ("EVAL: " ++ show e)
                  stop <- liftIO getCurrentTime
                  let time = diffUTCTime stop start
                      secs = read (takeWhile (/='.') (init (show time)))
                      rest = read ('0':dropWhile (/='.') (init (show time)))
                      mins = secs `quot` 60
                      sec  = printf "%.3f" (fromInteger (secs `rem` 60) + rest :: Float)
                  when (Time `elem` flags) $
                    outputStrLn $ "Time: " ++ show mins ++ "m" ++ sec ++ "s"
                  -- Only print in seconds:
                  -- when (Time `elem` flags) $ outputStrLn $ "Time: " ++ show time
                  loop flags f names tenv

-- (not ok,loaded,already loaded defs) -> to load ->
--   (new not ok, new loaded, new defs)
-- the bool determines if it should be verbose or not
imports :: Bool -> ([String],[String],[Module]) -> String ->
           IO ([String],[String],[Module])
imports v st@(notok,loaded,mods) f
  | f `elem` notok  = putStrLn ("Looping imports in " ++ f) >> return ([],[],[])
  | f `elem` loaded = return st
  | otherwise       = do
    b <- doesFileExist f
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
              when (name /= dropExtension (takeFileName f)) $
                error $ "Module name mismatch " ++ show (f,name)
              (notok1,loaded1,mods1) <-
                foldM (imports v) (f:notok,loaded,mods) imp_cub
              when v $ putStrLn $ "Parsed " ++ show f ++ " successfully!"
              return (notok,f:loaded1,mods1 ++ [mod])

help :: String
help = "\nAvailable commands:\n" ++
       "  <expr>          evaluate an expression\n" ++
       "  :q              quit\n" ++
       "  :l <filename>   loads filename (and resets environment before)\n" ++
       "  :cd <path>      change directory to path\n" ++
       "  :r              reload\n" ++
       "  :h              display this message\n" ++
       "  :n <expr>       normalize an expression\n"
