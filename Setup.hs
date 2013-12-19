import Distribution.Simple
import System.Process
main = do system "bnfc -d Exp.cf"
          defaultMain
