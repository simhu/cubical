module Main where

import Control.Monad.Trans
import Control.Monad.Trans.Reader
import Data.List
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
import qualified Eval as E

type Interpreter = InputT IO

defaultPrompt :: String
defaultPrompt = "> "

lexer :: String -> [Token]
lexer = resolveLayout True . myLexer

showTree :: (Show a, Print a) => a -> IO ()
showTree tree = do
  putStrLn $ "\n[Abstract Syntax]\n\n" ++ show tree
  putStrLn $ "\n[Linearized tree]\n\n" ++ printTree tree

parseFiles :: [FilePath] -> IO ([Imp],[Def])
parseFiles []     = return ([],[])
parseFiles (f:fs) = do
  s <- readFile f
  let ts = lexer s
  case pModule ts of
    Bad s  -> do
      putStrLn $ "Parse Failed in file " ++ show f ++ "\n"
      putStrLn $ "Tokens: " ++ show ts
      putStrLn s
      return ([],[])
    Ok mod@(Module _ imps defs) -> do
      putStrLn $ "Parsed file " ++ show f ++ " successfully!"
      showTree mod
      (imps',defs') <- parseFiles fs
      return $ (imps ++ imps',defs ++ defs')

main :: IO ()
main = getArgs >>= runInputT defaultSettings . runInterpreter

--  names to import -> files already imported -> all definitions
imports :: [String] -> [FilePath] -> [Def] -> Interpreter [Def]
imports [] _  defs = return defs
imports xs fs defs = do
  (imps,newDefs) <- lift $ parseFiles xs
  let imps' = [ unIdent s ++ ".cub" | Import s <- imps ]
  imports (nub imps' \\ fs) (fs ++ xs) (defs ++ newDefs)

runInterpreter :: [FilePath] -> Interpreter ()
runInterpreter fs = do
  -- parse and type-check files
  defs <- imports fs [] []
  let cg = callGraph defs
  let ns = defsToNames $ concat $ concat cg
  -- Compute all constructors
  let cs = concat [ [ unIdent n | Sum n _ <- lbls] | DefData _ _ lbls <- defs ]
  let res = runResolver (local (insertConstrs cs) (handleMutuals cg))
  outputStrLn $ "res = " ++ show res
  case res of
    Left err -> outputStrLn $ "Resolver failed: " ++ err
    Right re -> let term = handleLet A.Top re in
      case A.checkExp term of
        Left err -> outputStrLn $ "Type checking failed: " ++ err
        Right () -> do
          outputStrLn $ "Files loaded."
          loop (Env ns cs) re
  where
    -- TODO: All the concrete to abstract to internal should be more
    -- modular so that we don't have to repeat the translations.
    loop :: Env -> [[([String],A.Exp,A.Exp)]] -> InputT IO ()
    loop env re = do
      input <- getInputLine defaultPrompt
      case input of
        Nothing    -> outputStrLn help >> loop env re
        Just ":q"  -> return ()
        Just ":r"  -> runInterpreter fs
        Just ":h"  -> outputStrLn help >> loop env re
        Just str   -> let ts = lexer str in
          case pExp ts of
            Bad err -> outputStrLn ("Parse error: " ++ err) >> loop env re
            Ok exp  ->
              case runResolver (local (const env) (resolveExp exp)) of
                Left err   -> outputStrLn ("Resolver failed: " ++ err) >> loop env re
                Right body -> let term = handleLet body re in
                  case A.checkExpInfer term of
                    Left err -> outputStrLn ("Could not type-check: " ++ err) >> loop env re
                    Right _  -> case translate term of
                      Left err -> outputStrLn ("Could not translate to internal syntax: " ++ err) >>
                                  loop env re
                      Right t  -> let value = E.eval E.Empty t in
                        outputStrLn ("EVAL: " ++ show value) >> loop env re

help :: String
help = "\nAvailable commands:\n" ++
       "  <statement>     infer type and evaluate statement\n" ++
       "  :q              quit\n" ++
       "  :r              reload\n" ++
       "  :h              display this message\n"
