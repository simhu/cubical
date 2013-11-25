module Main where

import Control.Monad.Trans
import Control.Monad.Trans.Reader
import System.Environment
import System.Console.Haskeline
import Exp.Lex
import Exp.Par
import Exp.Skel
import Exp.Print
import Exp.Abs
import Exp.Layout
import Exp.ErrM
import AbsToInternal
import Concrete
import qualified MTT as A
import Eval

type Verbosity = Int

defaultVerbosity :: Verbosity
defaultVerbosity = 2

defaultPrompt :: String
defaultPrompt = "> "

lexer :: String -> [Token]
lexer = resolveLayout True . myLexer


-- TODO: fix
putStrLnV _ = putStrLn

-- TODO: fix
showTreeV :: (Show a, Print a) => Verbosity -> a -> IO ()
showTreeV _ tree = do
  putStrLn $ "\n[Abstract Syntax]\n\n" ++ show tree
  putStrLn $ "\n[Linearized tree]\n\n" ++ printTree tree


unModule :: Module -> [Def]
unModule (Module defs) = defs
unModule (ModEval _ defs) = defs

parseFiles :: Verbosity -> [FilePath] -> IO [Def]
parseFiles _ [] = return []
parseFiles v (f:fs) = do
  s <- readFile f
  let ts = lexer s
  case pModule ts of
    Bad s  -> do
      putStrLn $ "Parse Failed in file " ++ show f ++ "\n"
      putStrLnV v $ "Tokens: " ++ show ts
      putStrLn s
      return []
    Ok mod -> do
      putStrLnV v $ "Parsed file " ++ show f ++ " successfully!"
      showTreeV v mod
      defs <- parseFiles v fs
      return $ unModule mod ++ defs

main :: IO ()
main = getArgs >>= (runInputT defaultSettings . runInterpreter defaultVerbosity)

-- TODO: Spaghetti ftw!!
runInterpreter :: Verbosity -> [FilePath] -> InputT IO ()
runInterpreter v fs = do
  -- parse and type-check files
  defs <- lift $ parseFiles v fs
  let cg = callGraph defs
  let ns = defsToNames $ concat $ concat cg
  let res = runResolver (handleMutuals cg)
  case res of
    Left err -> outputStrLn $ "Resolver failed: " ++ err
    Right re -> let term = handleLet A.Top re in
      case A.checkExp term of
        Left err -> outputStrLn $ "Type checking failed: " ++ err
        Right () -> do
          outputStrLn $ "Files loaded."
          loop ns re
  where
    -- TODO: All the concrete to abstract to internal should be more
    -- modular so that we don't have to repeat the translations.
    loop :: [String] -> [[([String],A.Exp,A.Exp)]] -> InputT IO ()
    loop ns re = do
      input <- getInputLine defaultPrompt
      case input of
        Nothing    -> outputStrLn help >> loop ns re
        Just ":q"  -> return ()
        Just ":r"  -> runInterpreter v fs
        Just ":h"  -> outputStrLn help >> loop ns re
        Just str   -> let ts = lexer str in
          case pExp ts of
            Bad err -> -- putStrLn "\nParse Failed in file " ++ show f ++ "\n"
                     -- putStrLnV v $ "Tokens: " ++ show ts
                     outputStrLn ("Parse error: " ++ err) >> loop ns re
            Ok exp  ->
              case runResolver (local (insertNames ns) $ resolveExp exp) of
                Left err   -> outputStrLn ("Resolver failed: " ++ err) >> loop ns re
                Right body -> let term = handleLet body re in
                  case A.checkExpInfer term of
                    Left err -> outputStrLn ("Could not type-check: " ++ err) >> loop ns re
                    Right _  -> case translate term of
                      Left err -> outputStrLn ("Could not translate to internal syntax: " ++ err) >>
                                  loop ns re
                      Right t  -> let value = eval [] Empty t in
                        outputStrLn ("EVAL: " ++ show value) >> loop ns re

help :: String
help = "\nAvailable commands:\n" ++
       "  <statement>     infer type and evaluate statement\n" ++
       "  :q              quit\n" ++
       "  :r              reload\n" ++
       "  :h              display this message\n"


--  xs <- parseFiles fs
--  runInputT defaultSettings (loop (evalFiles xs []))
  where

-- main :: IO ()
-- main = do
--   (f:_) <- getArgs -- for the moment just bother about one input file
--   s     <- readFile f
--   let ts = myLLexer s
--   case pModule ts of
--     Bad s    -> do
--       putStrLn "\nParse Failed...\n"
--       putStrLn $ "Tokens:\n" ++ show ts
--       putStrLn s
--     Ok  tree -> do
--       putStrLn "\nParse Successful!"
--       showTree tree
--       let g = map (\(_,y,z) -> (y,z)) $ graph (unModule tree)
--       putStrLn $ "\nGraph:\n" ++ show g
--       let cg = map (map (concatMap defToNames)) $ callGraph $ unModule tree
-- --      let cg = callGraph $ unModule tree
--       putStrLn $ "\nCall graph:\n" ++ show cg
--       case runResolver (handleModule tree) of
--         Left err  -> putStrLn $ "\nResolver Failed: " ++ err
--         Right exp -> do
--           putStrLn "\nResolver Successful!"
--           putStrLn $ show exp ++ "\n"
--           case A.checkExpInfer exp of
--             Left terr -> putStrLn $ "\nType checking failed: " ++ show terr
--             Right _   ->
--               do putStrLn "YES!!!"
--                  case translate exp of
--                    Left err -> putStrLn $ "\nTranslation failed: " ++ show err
--                    Right ter -> do
--                      putStrLn $ "Translation: " ++ show ter
--                      putStrLn $ "Eval: " ++ show (eval [] Empty ter)

-- unModule (Module defs) = defs
-- unModule (ModEval _ defs) = defs
