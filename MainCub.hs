module Main where

import Control.Monad.Trans (lift)
import System.Console.Haskeline
import System.Environment
import qualified Text.ParserCombinators.Parsec as P

import Core
import Parser
import qualified Program as E
import Eval

main :: IO ()
main = getArgs >>= runInterpreter

runInterpreter :: [FilePath] -> IO ()
runInterpreter fs = do
  xs <- parseFiles fs
  runInputT defaultSettings (loop (evalFiles xs []))
  where
  parseFiles :: [FilePath] -> IO [(String,Ter)]
  parseFiles []     = return []
  parseFiles (f:fs) = do
    s <- readFile f
    case parse s of
      Right p  -> case fromProgram p of
        Right p -> parseFiles fs >>= \ps -> return (p ++ ps)
        Left e  -> putStrLn e >> return []
      Left err -> putStrLn ("Parse error in " ++ f ++ ": " ++ err) >> return []

  evalFiles :: [(String,Ter)] -> [Val] -> [(String,Val)]
  evalFiles [] _ = []
  evalFiles ((n,x):xs) env = (n,v) : evalFiles xs (env ++ [v])
    where v = eval [] env x

  -- The main loop. First match on the possible commands then parse and
  -- evaluate the expression.
  loop :: [(String,Val)] -> InputT IO ()
  loop env = do
    input <- getInputLine "cubigle> "
    case input of
      Nothing    -> outputStrLn help >> loop env
      Just ":q"  -> return ()
      Just ":r"  -> lift $ runInterpreter fs
      Just ":h"  -> outputStrLn help >> loop env
      Just input -> case parseExp input of
        Left err -> outputStrLn ("Parse error: " ++ err) >> loop env
        Right p  -> case eval [] (map snd env) p of
        -- TODO: Output Error from eval? Should not be necessary after type checking...
        -- Left err -> outputStrLn ("Eval error: " ++ err) >> loop env
        -- Right v  -> outputStrLn (show v) >> loop env
          v  -> outputStrLn (show v) >> loop env
    where
    parseExp :: String -> Either String Ter
    parseExp input = case P.parse (term >>= \x -> P.eof >> return x) "" input of
      Right e  -> removeNames (map fst env) e
      Left err -> Left $ show err

    help :: String
    help = "\nAvailable commands:\n" ++
           "  <statement>     infer type and evaluate statement\n" ++
           "  :q              quit\n" ++
           "  :r              reload\n" ++
           "  :h              display this message\n"
