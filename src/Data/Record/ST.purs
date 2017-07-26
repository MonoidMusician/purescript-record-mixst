module Data.Record.ST where

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

newtype MIxSTEff
  (realm :: Type)
  (fromVars :: # Type)
  (toVars :: # Type)
  (eff :: # Effect)
  (ret :: Type)
  = MIxSTEff
    ( Record fromVars ->
      STEff realm eff
      ( Tuple ret (Record toVars) )
    )
derive instance newtypeMIxSTEff :: Newtype (MIxSTEff r f t e d) _

type MIxSTREff
  (realm :: Type)
  (fromVars :: # Type)
  (toVars :: # Type)
  (eff :: # Effect)
  (r :: # Type)
  (m :: # Type)
  = MIxSTEff realm fromVars toVars eff (STRecord realm r m)

type STEff realm eff
  = Eff (st :: ST realm | eff)

type OnSTRecord realm eff r m a
  = STRecord realm r m -> STEff realm eff a

type MutSTRecord realm eff r r' m m'
  = OnSTRecord realm eff r m (STRecord realm r' m')

runMIxSTEff ::
  forall realm fromVars toVars eff ret.
  MIxSTEff realm fromVars toVars eff ret ->
  Record fromVars -> Eff (st :: ST realm | eff) (Tuple ret (Record toVars))
runMIxSTEff (MIxSTEff f) = f

rbind ::
  forall realm x y z eff a b.
        MIxSTEff realm x y   eff a ->
  (a -> MIxSTEff realm   y z eff b) ->
        MIxSTEff realm x   z eff b
rbind (MIxSTEff start) next =
  MIxSTEff \vars -> start vars >>= \(Tuple a s) ->
    runMIxSTEff (next a) s
infixl 1 rbind as >>~

rpure ::
  forall realm vars eff a.
  a -> MIxSTEff realm vars vars eff a
rpure = MIxSTEff <<< curry Monad.pure

rliftEff ::
  forall realm vars eff ret.
  Eff (st :: ST realm | eff) ret ->
  MIxSTEff realm vars vars eff ret
rliftEff e = MIxSTEff \vars -> e <#> flip Tuple vars

pureMIxSTEff ::
  forall realm vars vars' eff ret.
  (Record vars -> Tuple ret (Record vars')) ->
  MIxSTEff realm vars vars' eff ret
pureMIxSTEff f = MIxSTEff (pure <<< f)

withMIxSTEff ::
  forall realm vars eff ret.
  (Record vars -> ret) ->
  MIxSTEff realm vars vars eff ret
withMIxSTEff f = pureMIxSTEff \vars -> Tuple (f vars) vars

mapMIxSTEff ::
  forall realm vars vars' eff ret.
  (Record vars -> Record vars') ->
  MIxSTEff realm vars vars eff ret ->
  MIxSTEff realm vars vars' eff ret
mapMIxSTEff f start = start >>~ \v -> pureMIxSTEff (Tuple v <<< f)

getV ::
  forall name realm meh vars eff r m.
    IsSymbol name =>
    RowCons name (STRecord realm r m) meh vars =>
  SProxy name ->
  MIxSTREff realm vars vars eff r m
getV name = MIxSTEff \vars -> pure (Tuple (R.get name vars) vars)

setV ::
  forall name r r' realm vars meh vars' eff r m.
    IsSymbol name =>
    RowCons name (STRecord realm r m) meh vars =>
    RowCons name (STRecord realm r' m) meh vars' =>
  SProxy name ->
  STRecord realm r' m ->
  MIxSTEff realm vars vars' eff Unit
setV name entry = MIxSTEff \vars -> pure (Tuple unit (R.set name entry vars))

insertV ::
  forall name r realm vars vars' eff r m.
    IsSymbol name =>
    RowLacks name vars =>
    RowCons name (STRecord realm r m) vars vars' =>
  SProxy name ->
  STRecord realm r m ->
  MIxSTEff realm vars vars' eff Unit
insertV name entry = MIxSTEff \vars -> pure (Tuple unit (R.insert name entry vars))

modifyV ::
  forall name r r' realm vars meh vars' eff r m.
    IsSymbol name =>
    RowCons name (STRecord realm r m) meh vars =>
    RowCons name (STRecord realm r' m) meh vars' =>
  SProxy name ->
  (STRecord realm r m -> Eff (st :: ST realm | eff) (STRecord realm r' m)) ->
  MIxSTEff realm vars vars' eff Unit
modifyV name f = getV name >>~ f >>> rliftEff >>~ setV name

thawAs ::
  forall name vars vars' realm r eff.
    IsSymbol name =>
    RowLacks name vars =>
    RowCons name (STRecord realm r ()) vars vars' =>
  SProxy name -> Record r ->
  MIxSTEff realm vars vars' eff Unit
thawAs name r = rliftEff (rawCopy r) >>~ insertV name

freezeFrom ::
  forall name meh vars realm r eff.
    IsSymbol name =>
    RowCons name (STRecord realm r ()) meh vars =>
  SProxy name ->
  MIxSTEff realm vars vars eff (Record r)
freezeFrom name = getV name >>~ rliftEff <<< rawCopy

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
  forall r m b realm eff.
  String -> OnSTRecord realm eff r m Unit

unmanagedGet ::
  forall sym t r r' m realm vars eff.
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
  MIxSTEff realm vars vars eff t
get name k = getV name >>~ unmanagedGet k >>> rliftEff

unmanagedTest ::
  forall sym t r m m' realm vars eff.
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
  MIxSTEff realm vars vars eff Boolean
test name k = getV name >>~ unmanagedTest k >>> rliftEff

unmanagedGetM ::
  forall sym t r m m' realm vars eff.
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
  MIxSTEff realm vars vars eff (Maybe t)
getM name k = getV name >>~ unmanagedGetM k >>> rliftEff

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
  t -> MIxSTEff realm vars vars' eff Unit
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
  MIxSTEff realm vars vars' eff Unit
delete name k = modifyV name $ unmanagedDelete k
