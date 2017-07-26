module Control.IxMonad.State.Class where

import Control.IxMonad (class IxMonad, ipure, (=<<:))
import Control.Semigroupoid ((<<<))
import Data.Unit (Unit)

class IxMonad m <= IxMonadState m where
  iget :: forall i. m i i i
  iput :: forall i j. j -> m i j Unit

imodify :: forall m i j. IxMonadState m => (i -> j) -> m i j Unit
imodify f = iput <<< f =<<: iget

igets :: forall m i a. IxMonadState m => (i -> a) -> m i i a
igets f = ipure <<< f =<<: iget
