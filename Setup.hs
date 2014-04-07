import Control.Monad
import Distribution.Simple
import System.Directory
import System.Process
import System.Exit

main :: IO ()
main = do
  b  <- doesFileExist "Exp/Abs.hs"
  -- run bnfc if Exp/Abs.hs does not exist
  when (not b) bnfc
  t1 <- getModificationTime "Exp.cf"
  t2 <- getModificationTime "Exp"
  -- run bnfc if Exp.cf has been modified
  when (t1 > t2) bnfc
  defaultMain
  where
    bnfc = do
      ret <- system "bnfc --haskell -d Exp.cf"
      case ret of
        ExitSuccess   -> defaultMain
        ExitFailure n -> error $ "bnfc command not found or error" ++ show n
