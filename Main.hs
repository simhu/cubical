module Main where

import Control.Monad.Trans
import Control.Monad.Trans.State
import Control.Monad.Trans.Reader
import Control.Monad.Identity
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
import SimpConcrete
import qualified MTT as A
import qualified Eval as E

type Interpreter a = StateT A.LEnv (InputT IO) a

outputLn :: String -> Interpreter ()
outputLn = lift . outputStrLn

defaultPrompt :: String
defaultPrompt = "> "

lexer :: String -> [Token]
lexer = resolveLayout True . myLexer

showTree :: (Show a, Print a) => a -> IO ()
showTree tree = do
  putStrLn $ "\n[Abstract Syntax]\n\n" ++ show tree
  putStrLn $ "\n[Linearized tree]\n\n" ++ printTree tree

parseFiles :: [FilePath] -> Interpreter ([Imp],[Def])
parseFiles []     = return ([],[])
parseFiles (f:fs) = do
  s <- lift $ lift $ readFile f
  let ts = lexer s
  case pModule ts of
    Bad s  -> do
      outputLn $ "Parse Failed in file " ++ show f ++ "\n"
--      outputLn $ "Tokens: " ++ show ts
      outputLn s
      return ([],[])
    Ok mod@(Module _ imps defs) -> do
      outputLn $ "Parsed file " ++ show f ++ " successfully!"
--      showTree mod
      (imps',defs') <- parseFiles fs
      return $ (imps ++ imps',defs ++ defs')

main :: IO ()
main = getArgs >>= runInputT defaultSettings . (`evalStateT` A.lEmpty) . runInterpreter

--  names to import -> files already imported -> all definitions
imports :: [String] -> [FilePath] -> [Def] -> Interpreter [Def]
imports [] _  defs = return defs
imports xs fs defs = do
  (imps,newDefs) <- parseFiles xs
  let imps' = [ unIdent s ++ ".cub" | Import s <- imps ]
  imports (nub imps' \\ fs) (fs ++ xs) (defs ++ newDefs)

runInterpreter :: [FilePath] -> Interpreter ()
runInterpreter fs = do
  -- parse and type-check files
  defs <- imports fs [] []
  -- Compute all constructors
  let cs = concat [ [ unIdent n | Sum n _ <- lbls] | DefData _ _ lbls <- defs ]
  let res = runResolver (local (insertConstrs cs) (concrToAbs defs))
  case res of
    Left err    -> outputLn $ "Resolver failed: " ++ err
    Right adefs -> case A.runDefs A.lEmpty adefs of
      Left err   -> outputLn $ "Type checking failed: " ++ err
      Right lenv -> do
        modify (const lenv)
        outputLn $ "Files loaded."
        loop cs
  where
    -- TODO: All the concrete to abstract to internal should be more
    -- modular so that we don't have to repeat the translations.
    loop :: [String] -> Interpreter ()
    loop cs = do
      input <- lift (getInputLine defaultPrompt)
      case input of
        Nothing    -> outputLn help >> loop cs
        Just ":q"  -> return ()
        Just ":r"  -> runInterpreter fs
--        Just (":l":xs) -> runInterpreter (words xs)
        Just ":h"  -> outputLn help >> loop cs
        Just str   -> let ts = lexer str in
          case pExp ts of
            Bad err -> outputLn ("Parse error: " ++ err) >> loop cs
            Ok exp  ->
              case runResolver (local (const (Env cs)) (resolveExp exp)) of
                Left err   -> outputLn ("Resolver failed: " ++ err) >> loop cs
                Right body -> do
                  lenv <- get
                  case A.runInfer lenv body of
                    Left err -> outputLn ("Could not type-check: " ++ err) >> loop cs
                    Right _  -> do
                      (_,rho,_) <- get
                      case translate (A.defs rho body) of
                        Left err -> outputLn ("Could not translate to internal syntax: " ++ err) >>
                                    loop cs
                        Right t  -> let value = E.eval E.Empty t in
                          outputLn ("EVAL: " ++ show value) >> loop cs

help :: String
help = "\nAvailable commands:\n" ++
       "  <statement>     infer type and evaluate statement\n" ++
       "  :q              quit\n" ++
       "  :r              reload\n" ++
       "  :h              display this message\n"
