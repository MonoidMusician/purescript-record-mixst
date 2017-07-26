module Control.IxMonad.State.MVIxSTEff where

import Control.IxMonad.State.IxSTEff (IxSTEff(..), STEff)
import Prelude (Unit, pure, ($), (<<<), (>>>))

import Control.IxMonad (ibind, ipure, (:>>=))
import Control.IxMonad.State.Class (imodify, igets)
import Control.Monad.Eff (kind Effect)
import Control.Monad.Eff.Class (liftEff)
import Data.Record as R
import Data.Tuple (Tuple(..))
import Type.Prelude (SProxy, class IsSymbol, class RowLacks)

type MVIxSTEff
  (realm :: Type)
  (eff :: # Effect)
  (fromVars :: # Type)
  (toVars :: # Type)
  (ret :: Type)
  = IxSTEff realm eff (Record fromVars) (Record toVars) ret

runMVIxSTEff :: forall realm fromVars toVars eff ret.
  MVIxSTEff realm eff fromVars toVars ret ->
  Record fromVars -> STEff realm eff (Tuple ret (Record toVars))
runMVIxSTEff (IxSTEff f) = f

mvbind :: forall   realm eff x y z a b.
        MVIxSTEff realm eff x y   a  ->
  (a -> MVIxSTEff realm eff   y z b) ->
        MVIxSTEff realm eff x   z b
mvbind = ibind

mvpure :: forall realm eff vars a.
  a -> MVIxSTEff realm eff vars vars a
mvpure = ipure

mvbindLift :: forall realm eff x y a b.
  MVIxSTEff realm eff x y a ->
  (a -> STEff realm eff b) ->
  MVIxSTEff realm eff x y b
mvbindLift start f = start :>>= f >>> mvliftEff
infixl 1 mvbindLift as :>>=/

mvliftBind :: forall realm x y eff a b.
  STEff realm eff a ->
  (a -> MVIxSTEff realm eff x y b) ->
  MVIxSTEff realm eff x y b
mvliftBind start f = mvliftEff start :>>= f
infixl 1 mvliftBind as /:>>=

mvliftEff :: forall realm eff vars ret.
  STEff realm eff ret ->
  MVIxSTEff realm eff vars vars ret
mvliftEff = liftEff

pureMVIxSTEff :: forall realm eff vars vars' ret.
  (Record vars -> Tuple ret (Record vars')) ->
  MVIxSTEff realm eff vars vars' ret
pureMVIxSTEff f = IxSTEff (pure <<< f)

withMVIxSTEff :: forall realm eff vars ret.
  (Record vars -> ret) ->
  MVIxSTEff realm eff vars vars ret
withMVIxSTEff f =
  pureMVIxSTEff \vars -> Tuple (f vars) vars

mapMVIxSTEff :: forall realm eff vars vars' ret.
  (Record vars -> Record vars') ->
  MVIxSTEff realm eff vars vars ret ->
  MVIxSTEff realm eff vars vars' ret
mapMVIxSTEff f start =
  start :>>= \v -> pureMVIxSTEff (Tuple v <<< f)

getV ::
  forall name realm eff meh vars d.
    IsSymbol name =>
    RowCons name d meh vars =>
  SProxy name ->
  MVIxSTEff realm eff vars vars d
getV name =
  igets $ R.get name

setV ::
  forall name realm eff vars meh vars' d d'.
    IsSymbol name =>
    RowCons name d meh vars =>
    RowCons name d' meh vars' =>
  SProxy name ->
  d' ->
  MVIxSTEff realm eff vars vars' Unit
setV name entry =
  imodify $ R.set name entry

insertV ::
  forall name realm eff vars vars' d.
    IsSymbol name =>
    RowLacks name vars =>
    RowCons name d vars vars' =>
  SProxy name ->
  d ->
  MVIxSTEff realm eff vars vars' Unit
insertV name entry =
  imodify $ R.insert name entry

deleteV ::
  forall name realm eff vars meh vars' d.
    IsSymbol name =>
    RowLacks name vars' =>
    RowCons name d vars' vars =>
  SProxy name ->
  MVIxSTEff realm eff vars vars' Unit
deleteV name =
  imodify $ R.delete name

modifyV ::
  forall name realm eff vars meh vars' d d'.
    IsSymbol name =>
    RowCons name d meh vars =>
    RowCons name d' meh vars' =>
  SProxy name ->
  (d -> STEff realm eff d') ->
  MVIxSTEff realm eff vars vars' Unit
modifyV name f =
  getV name :>>=/ f :>>= setV name
