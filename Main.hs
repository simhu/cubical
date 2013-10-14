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
  -- TODO: Do something with the files!
  xs <- parseFiles fs
  runInputT defaultSettings (loop [] [])
  where 
  parseFiles :: [FilePath] -> IO [[(String,Ter)]]
  parseFiles []     = return []
  parseFiles (f:fs) = do
    s <- readFile f
    case parse s of
      Right p  -> do
        xs <- parseFiles fs
        return (fromProgram p ++ xs)      
      Left err -> putStrLn ("Parse error in " ++ f ++ ": " ++ err) >> return []
  
  -- The main loop. First match on the possible commands then parse and
  -- evaluate the expression.
  loop :: [(String,Ter)] -> [(String,Ter)] -> InputT IO ()
  loop env ctx = do
    input <- getInputLine "> "
    case input of
      Nothing   -> loop env ctx
      Just ":q" -> return ()
      Just ":r" -> lift $ runInterpreter fs
      Just ":h" -> outputStrLn help >> loop env ctx
      Just input -> case parseExp input of
        Left err -> outputStrLn ("Parse error: " ++ err) >> loop env ctx
        -- TODO: Call eval' with the environment!
        Right p  -> case eval' [] [] p of
--          Left err -> outputStrLn ("Eval error: " ++ err) >> loop env ctx
--          Right v  -> outputStrLn (show v) >> loop env ctx
         -- TODO: Output Error from eval'? 
         v  -> outputStrLn (show v) >> loop env ctx
    where
    parseExp :: String -> Either String Ter
    parseExp input = case P.parse (term >>= \x -> P.eof >> return x) "" input of
      Right e  -> Right $ removeNames e
      Left err -> Left $ show err
 
    help :: String
    help = "\nAvailable commands:\n" ++ 
           "  <statement>     infer type and evaluate statement\n" ++
           "  :q              quit\n" ++
           "  :r              reload\n" ++
           "  :h              display this message\n"
