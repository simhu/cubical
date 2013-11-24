module Main where

import Concrete
import qualified MTT as A
import System.Environment

import Exp.Lex
import Exp.Par
import Exp.Skel
import Exp.Print
import Exp.Abs
import Exp.Layout
import Exp.ErrM
import AbsToInternal
import Eval

myLLexer = resolveLayout True . myLexer

showTree :: (Show a, Print a) => a -> IO ()
showTree tree = do
  putStrLn $ "\n[Abstract Syntax]\n\n" ++ show tree
  putStrLn $ "\n[Linearized tree]\n\n" ++ printTree tree

main :: IO ()
main = do
  (f:_) <- getArgs -- for the moment just bother about one input file
  s     <- readFile f
  let ts = myLLexer s
  case pModule ts of
    Bad s    -> do
      putStrLn "\nParse Failed...\n"
      putStrLn $ "Tokens:\n" ++ show ts
      putStrLn s
    Ok  tree -> do
      putStrLn "\nParse Successful!"
      showTree tree
      let g = map (\(_,y,z) -> (y,z)) $ graph (unModule tree)
      putStrLn $ "\nGraph:\n" ++ show g
      let cg = map (map (concatMap defToNames)) $ callGraph $ unModule tree
--      let cg = callGraph $ unModule tree
      putStrLn $ "\nCall graph:\n" ++ show cg
      case runResolver (handleModule tree) of
        Left err  -> putStrLn $ "\nResolver Failed: " ++ err
        Right exp -> do
          putStrLn "\nResolver Successful!"
          putStrLn $ show exp ++ "\n"
          case A.checkExpInfer exp of
            Left terr -> putStrLn $ "\nType checking failed: " ++ show terr
            Right _   ->
              do putStrLn "YES!!!"
                 case translate exp of
                   Left err -> putStrLn $ "\nTranslation failed: " ++ show err
                   Right ter -> do
                     putStrLn $ "Translation: " ++ show ter
                     putStrLn $ "Eval: " ++ show (eval [] Empty ter)

unModule (Module defs) = defs
unModule (ModEval _ defs) = defs
