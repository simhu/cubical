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
      putStrLn $ "DEBUG: " ++ show tree
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

-- checkMain :: A.Exp ->         
          

unModule (Module defs) = defs
unModule (ModEval _ defs) = defs


--  Where (Where (Where (App (Var 0) (Var 1)) [Branch [("zero",Con "zero" []),("suc",Con "zero" [])]]) [Con "suc" [Con "suc" [Con "zero" []]]]) [LSum [("zero",[]),("suc",[Var 0])]]

--Where (Where (Where (Where (Where (Where (Where (Where (Where (Where (Where (Where (Where (Where (Where (Where (Where (Var 0) [App (App (App (App (App (App (Var 3) (Pi (Var 16) (Lam (Var 17)))) (Var 16)) (Var 9)) (Var 15)) (Var 11)) (Var 1)]) [App (App (App (App (App (Var 5) (Var 15)) (Lam (Var 16))) (Var 14)) (Var 10)) (Var 1)]) [Branch [("zero",App (App (Var 3) (Var 14)) (Con "zero" [])),("suc",App (App (App (App (App (App (Var 2) (Var 15)) (Var 15)) (Var 13)) (App (Var 14) (Var 0))) (App (Var 10) (Var 0))) (App (Var 1) (Var 0)))]]) [Lam (Lam (Lam (Lam (Lam (Lam (App (App (App (App (App (App (Var 7) (Var 5)) (Lam (App (App (App (Var 11) (Var 5)) (App (Var 4) (Var 3))) (App (Var 4) (Var 0))))) (Var 2)) (Var 1)) (Var 0)) (App (App (Var 8) (Var 4)) (App (Var 3) (Var 2)))))))))]) [Lam (Lam (Lam (Lam (Lam (Lam (Trans (Var 4) (Var 1) (Var 0)))))))]) [Lam (Lam (App (Refl (Var 1)) (Var 0)))]) [Lam (Lam (Lam (Lam (Lam (Ext (Var 3) (Var 2) (Var 1) (Var 0))))))]) [Lam (Lam (Lam (Id (Var 2) (Var 1) (Var 0))))]) [Con "zero" []]) [Lam (App (App (Var 2) (App (Var 0) (Var 5))) (App (Var 0) (Var 4)))]) [Branch [("zero",Lam (Var 0)),("suc",Lam (Con "suc" [App (App (Var 2) (Var 1)) (Var 0)]))]]) [Branch [("zero",Con "zero" []),("suc",Con "suc" [App (Var 1) (Var 0)])]]) [Con "suc" [Var 1]]) [Con "suc" [Con "suc" [Con "zero" []]]]) [Lam (Con "suc" [Var 0])]) [Lam (Var 0)]) [LSum [("zero",[]),("suc",[Var 0])]]


-- Where (Where (Where (Where (Var 0) [App (App (Var 1) (Var 3)) (Con "zero" [])]) [Lam (Lam (App (Refl (Var 1)) (Var 0)))]) [Lam (Lam (Lam (Id (Var 2) (Var 1) (Var 0))))]) [LSum [("zero",[]),("suc",[Var 0])]]



--  Where  (App (App (Lam (Lam (App (Refl (Var 1)) (Var 0)))) (Var 1)) (Con "zero" [])) [LSum [("zero",[]),("suc",[Var 0])]]