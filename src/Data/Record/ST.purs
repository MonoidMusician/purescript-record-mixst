module Data.Record.ST where

import Control.IxMonad (class IxMonad, (:>>=))
import Control.Monad as Monad
import Control.Monad.Eff (Eff, kind Effect)
import Control.Monad.ST (ST)
import Control.Plus (empty)
import Data.Maybe (Maybe(..))
import Data.Newtype (class Newtype)
import Data.Record as R
import Data.Tuple (Tuple(..), curry)
import Prelude hiding (bind)
import Type.Prelude (class IsSymbol, class RowLacks, SProxy, reflectSymbol)
import Unsafe.Coerce (unsafeCoerce)

-- | Realm, guaranteed keys, optional keys
foreign import data STRecord :: Type -> # Type -> # Type -> Type

unsafeCoerceSTRecord ::
  forall realm r m r' m'.
  STRecord realm r m ->
  STRecord realm r' m'
unsafeCoerceSTRecord = unsafeCoerce

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

type MIxSTEff
  (realm :: Type)
  (eff :: # Effect)
  (fromVars :: # Type)
  (toVars :: # Type)
  (ret :: Type)
  = IxSTEff realm eff (Record fromVars) (Record toVars) ret

type MIxSTREff
  (realm :: Type)
  (eff :: # Effect)
  (fromVars :: # Type)
  (toVars :: # Type)
  (r :: # Type)
  (m :: # Type)
  = MIxSTEff realm eff fromVars toVars (STRecord realm r m)

type STEff realm eff
  = Eff (st :: ST realm | eff)

type OnSTRecord realm eff r m a
  = STRecord realm r m -> STEff realm eff a

type MutSTRecord realm eff r r' m m'
  = OnSTRecord realm eff r m (STRecord realm r' m')

instance ixMonadMIxSTEff :: IxMonad (IxSTEff realm eff) where
  ibind (IxSTEff start) next =
    IxSTEff \vars -> start vars >>= \(Tuple a s) ->
      runIxSTEff (next a) s
  ipure = IxSTEff <<< curry Monad.pure

runIxSTEff ::
  forall realm from to eff ret.
  IxSTEff realm eff from to ret ->
  from -> STEff realm eff (Tuple ret to)
runIxSTEff (IxSTEff f) = f

runMIxSTEff ::
  forall realm fromVars toVars eff ret.
  MIxSTEff realm eff fromVars toVars ret ->
  Record fromVars -> STEff realm eff (Tuple ret (Record toVars))
runMIxSTEff (IxSTEff f) = f

rbind ::
  forall realm x y z eff a b.
        MIxSTEff realm eff x y   a  ->
  (a -> MIxSTEff realm eff   y z b) ->
        MIxSTEff realm eff x   z b
rbind (IxSTEff start) next =
  IxSTEff \vars -> start vars >>= \(Tuple a s) ->
    runMIxSTEff (next a) s

rpure ::
  forall realm vars eff a.
  a -> MIxSTEff realm eff vars vars a
rpure = IxSTEff <<< curry Monad.pure

rliftEff ::
  forall realm vars eff ret.
  Eff (st :: ST realm | eff) ret ->
  MIxSTEff realm eff vars vars ret
rliftEff e = IxSTEff \vars -> e <#> Tuple <@> vars

pureMIxSTEff ::
  forall realm vars vars' eff ret.
  (Record vars -> Tuple ret (Record vars')) ->
  MIxSTEff realm eff vars vars' ret
pureMIxSTEff f = IxSTEff (pure <<< f)

withMIxSTEff ::
  forall realm vars eff ret.
  (Record vars -> ret) ->
  MIxSTEff realm eff vars vars ret
withMIxSTEff f = pureMIxSTEff \vars -> Tuple (f vars) vars

mapMIxSTEff ::
  forall realm vars vars' eff ret.
  (Record vars -> Record vars') ->
  MIxSTEff realm eff vars vars ret ->
  MIxSTEff realm eff vars vars' ret
mapMIxSTEff f start = start :>>= \v -> pureMIxSTEff (Tuple v <<< f)

getV ::
  forall name realm meh vars eff r m.
    IsSymbol name =>
    RowCons name (STRecord realm r m) meh vars =>
  SProxy name ->
  MIxSTREff realm eff vars vars r m
getV name = pureMIxSTEff \vars ->
  Tuple <@> vars $ R.get name vars

setV ::
  forall name realm vars meh vars' eff r r' m.
    IsSymbol name =>
    RowCons name (STRecord realm r m) meh vars =>
    RowCons name (STRecord realm r' m) meh vars' =>
  SProxy name ->
  STRecord realm r' m ->
  MIxSTEff realm eff vars vars' Unit
setV name entry = pureMIxSTEff $
  R.set name entry >>> Tuple unit

insertV ::
  forall name realm vars vars' eff r m.
    IsSymbol name =>
    RowLacks name vars =>
    RowCons name (STRecord realm r m) vars vars' =>
  SProxy name ->
  STRecord realm r m ->
  MIxSTEff realm eff vars vars' Unit
insertV name entry = pureMIxSTEff $
  R.insert name entry >>> Tuple unit

modifyV ::
  forall name realm vars meh vars' eff r r' m.
    IsSymbol name =>
    RowCons name (STRecord realm r m) meh vars =>
    RowCons name (STRecord realm r' m) meh vars' =>
  SProxy name ->
  (STRecord realm r m -> Eff (st :: ST realm | eff) (STRecord realm r' m)) ->
  MIxSTEff realm eff vars vars' Unit
modifyV name f =
  let g = f >>> rliftEff in
  getV name :>>= g :>>= setV name

thawAs ::
  forall name vars vars' realm r eff.
    IsSymbol name =>
    RowLacks name vars =>
    RowCons name (STRecord realm r ()) vars vars' =>
  SProxy name -> Record r ->
  MIxSTEff realm eff vars vars' Unit
thawAs name r = rliftEff (rawCopy r) :>>= insertV name

freezeFrom ::
  forall name meh vars realm r eff.
    IsSymbol name =>
    RowCons name (STRecord realm r ()) meh vars =>
  SProxy name ->
  MIxSTEff realm eff vars vars (Record r)
freezeFrom name = getV name :>>= rawCopy >>> rliftEff

foreign import rawCopy ::
  forall a b realm eff.
  a -> Eff (st :: ST realm | eff) b
foreign import rawExists ::
  forall r m realm eff.
  String -> OnSTRecord realm eff r m Boolean
foreign import rawGet ::
  forall r m b realm eff.
  String -> OnSTRecord realm eff r m b
foreign import rawSet ::
  forall r m v realm eff.
  String -> v -> OnSTRecord realm eff r m Unit
foreign import rawDelete ::
  forall r m realm eff.
  String -> OnSTRecord realm eff r m Unit

unmanagedGet ::
  forall sym t r r' m realm eff.
    IsSymbol sym =>
    RowCons sym t r' r =>
  SProxy sym ->
  OnSTRecord realm eff r m t
unmanagedGet = rawGet <<< reflectSymbol

get ::
  forall name sym t r r' m realm meh vars eff.
    IsSymbol name =>
    IsSymbol sym =>
    RowCons sym t r' r =>
    RowCons name (STRecord realm r m) meh vars =>
  SProxy name -> SProxy sym ->
  MIxSTEff realm eff vars vars t
get name k = getV name :>>= unmanagedGet k >>> rliftEff

unmanagedTest ::
  forall sym t r m m' realm eff.
    IsSymbol sym =>
    RowCons sym t m' m =>
  SProxy sym ->
  OnSTRecord realm eff r m Boolean
unmanagedTest k = rawExists (reflectSymbol k)

test ::
  forall name sym t r m m' realm meh vars eff.
    IsSymbol name =>
    IsSymbol sym =>
    RowCons sym t m' m =>
    RowCons name (STRecord realm r m) meh vars =>
  SProxy name -> SProxy sym ->
  MIxSTEff realm eff vars vars Boolean
test name k = getV name :>>= unmanagedTest k >>> rliftEff

unmanagedGetM ::
  forall sym t r m m' realm eff.
    IsSymbol sym =>
    RowCons sym t m' m =>
  SProxy sym ->
  OnSTRecord realm eff r m (Maybe t)
unmanagedGetM s r =
  let k = reflectSymbol s
  in rawExists k r >>=
    if _
      then Just <$> rawGet k r
      else pure empty

getM ::
  forall name sym t r m m' realm meh vars eff.
    IsSymbol name =>
    IsSymbol sym =>
    RowCons sym t m' m =>
    RowCons name (STRecord realm r m) meh vars =>
  SProxy name -> SProxy sym ->
  MIxSTEff realm eff vars vars (Maybe t)
getM name k = getV name :>>= unmanagedGetM k >>> rliftEff

unmanagedInsert ::
  forall sym t r r' m realm eff.
    IsSymbol sym =>
    RowLacks sym r =>
    RowCons sym t r r' =>
  SProxy sym -> t ->
  MutSTRecord realm eff r r' m m
unmanagedInsert s v r = do
  rawSet (reflectSymbol s) v r
  pure (unsafeCoerceSTRecord r)

insert ::
  forall name sym t r r' m realm vars meh vars' eff.
    IsSymbol name =>
    IsSymbol sym =>
    RowLacks sym r =>
    RowCons sym t r r' =>
    RowCons name (STRecord realm r m) meh vars =>
    RowCons name (STRecord realm r' m) meh vars' =>
  SProxy name -> SProxy sym ->
  t -> MIxSTEff realm eff vars vars' Unit
insert name k v = modifyV name $ unmanagedInsert k v

unmanagedDelete ::
  forall sym t r r' m realm eff.
    IsSymbol sym =>
    RowCons sym t r' r =>
    RowLacks sym r' =>
  SProxy sym ->
  MutSTRecord realm eff r r' m m
unmanagedDelete s r = do
  rawDelete (reflectSymbol s) r
  pure (unsafeCoerceSTRecord r)

delete ::
  forall name sym t r r' m realm vars meh vars' eff.
    IsSymbol name =>
    IsSymbol sym =>
    RowCons sym t r' r =>
    RowLacks sym r' =>
    RowCons name (STRecord realm r m) meh vars =>
    RowCons name (STRecord realm r' m) meh vars' =>
  SProxy name -> SProxy sym ->
  MIxSTEff realm eff vars vars' Unit
delete name k = modifyV name $ unmanagedDelete k
