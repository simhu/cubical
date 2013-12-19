import Distribution.Simple
import System.Process
import System.Exit
main = do
  ret <- system "bnfc -d Exp.cf"
  case ret of
    ExitSuccess   -> defaultMain
    ExitFailure n -> error $ "bnfc command not found or error" ++ show n
