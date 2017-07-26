module Control.IxMonad.State.IxSTEff where

import Control.IxMonad (class IxMonad, ibind, ipure)
import Control.IxMonad.State.Class (class IxMonadState)
import Control.Monad (class Applicative, class Apply, class Bind, class Functor, class Monad, ap, liftM1, pure, (>>=))
import Control.Monad.Eff (Eff, kind Effect)
import Control.Monad.Eff.Class (class MonadEff)
import Control.Monad.ST (ST)
import Control.Monad.State (class MonadState, get)
import Control.Semigroupoid ((<<<))
import Data.Function (const)
import Data.Functor ((<#>), (<@>))
import Data.Newtype (class Newtype)
import Data.Tuple (Tuple(..), curry)
import Data.Unit (unit)

type STEff realm eff
  = Eff (st :: ST realm | eff)

newtype IxSTEff
  (realm :: Type)
  (eff :: # Effect)
  (from :: Type)
  (to :: Type)
  (ret :: Type)
  = IxSTEff
    ( from ->
      STEff realm eff
      ( Tuple ret to )
    )
derive instance newtypeIxSTEff :: Newtype (IxSTEff r e f t d) _

instance functorIxSTEff :: Functor (IxSTEff realm eff x x) where
  map = liftM1
instance applyIxSTEff :: Apply (IxSTEff realm eff x x) where
  apply = ap
instance applicativeIxSTEff :: Applicative (IxSTEff realm eff x x) where
  pure = ipure
instance bindIxSTEff :: Bind (IxSTEff realm eff x x) where
  bind = ibind
instance monadIxSTEff :: Monad (IxSTEff realm eff x x)

instance monadStateIxSTEff :: MonadState x (IxSTEff realm eff x x) where
  state f = IxSTEff (pure <<< f)
instance monadEffIxSTEff :: MonadEff ( st :: ST realm | eff ) (IxSTEff realm eff x x) where
  liftEff e = IxSTEff \vars -> e <#> Tuple <@> vars

instance ixMonadIxSTEff :: IxMonad (IxSTEff realm eff) where
  ibind (IxSTEff start) next =
    IxSTEff \vars -> start vars >>= \(Tuple a s) ->
      runIxSTEff (next a) s
  ipure = IxSTEff <<< curry pure

instance ixMonadStateIxSTEff :: IxMonadState (IxSTEff realm eff) where
  iget = get
  iput = IxSTEff <<< const <<< pure <<< Tuple unit

runIxSTEff :: forall realm from to eff ret.
  IxSTEff realm eff from to ret ->
  from -> STEff realm eff (Tuple ret to)
runIxSTEff (IxSTEff f) = f
