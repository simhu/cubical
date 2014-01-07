{-# LANGUAGE TupleSections #-}
-- Tranlates the terms of MiniTT into the cubical syntax.
module MTTtoCTT where

import qualified CTT
import Control.Monad.Error
import Control.Applicative
-- import Control.Arrow
import Pretty


