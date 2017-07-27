module Control.IxMonad.State.IxStateT where

import Control.IxMonad (class IxMonad, ibind, ipure)
import Control.IxMonad.State.Class (class IxMonadState)
import Control.Monad (class Applicative, class Apply, class Bind, class Functor, class Monad, ap, liftM1, pure, (>>=))
import Control.Monad.Eff.Class (class MonadEff, liftEff)
import Control.Monad.State (class MonadState, get)
import Control.Semigroupoid ((<<<))
import Data.Function (const)
import Data.Functor ((<#>), (<@>))
import Data.Newtype (class Newtype)
import Data.Tuple (Tuple(..), curry)
import Data.Unit (unit)

newtype IxStateT
  (m :: Type -> Type)
  (from :: Type)
  (to :: Type)
  (ret :: Type)
  = IxStateT
    ( from -> m ( Tuple ret to ) )
derive instance newtypeIxStateT :: Newtype (IxStateT m f t d) _

instance functorIxStateT :: Monad m => Functor (IxStateT m x x) where
  map = liftM1
instance applyIxStateT :: Monad m => Apply (IxStateT m x x) where
  apply = ap
instance applicativeIxStateT :: Monad m => Applicative (IxStateT m x x) where
  pure = ipure
instance bindIxStateT :: Monad m => Bind (IxStateT m x x) where
  bind = ibind
instance monadIxStateT :: Monad m => Monad (IxStateT m x x)

instance monadStateIxStateT :: Monad m => MonadState x (IxStateT m x x) where
  state f = IxStateT (pure <<< f)
instance monadEffIxStateT :: MonadEff e m => MonadEff e (IxStateT m x x) where
  liftEff e = IxStateT \vars -> liftEff e <#> Tuple <@> vars

instance ixMonadIxStateT :: Monad m => IxMonad (IxStateT m) where
  ibind (IxStateT start) next =
    IxStateT \vars -> start vars >>= \(Tuple a s) ->
      runIxStateT (next a) s
  ipure = IxStateT <<< curry pure

instance ixMonadStateIxStateT :: Monad m => IxMonadState (IxStateT m) where
  iget = get
  iput = IxStateT <<< const <<< pure <<< Tuple unit

runIxStateT :: forall m from to ret.
  IxStateT m from to ret ->
  from -> m (Tuple ret to)
runIxStateT (IxStateT f) = f
