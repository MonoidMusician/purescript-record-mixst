module Data.Record.ST where

import Control.Alternative (class Alternative)
import Control.IxMonad (class IxMonad, ibind, ipure, (:>>=))
import Control.Monad as Monad
import Control.Monad.Eff (Eff, kind Effect)
import Control.Monad.Eff.Class (class MonadEff, liftEff)
import Control.Monad.ST (ST)
import Control.Monad.State as St
import Control.Monad.State.Class (class MonadState)
import Control.Plus (empty)
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

type VIxSTEff
  (realm :: Type)
  (eff :: # Effect)
  (fromVars :: # Type)
  (toVars :: # Type)
  (ret :: Type)
  = IxSTEff realm eff (Record fromVars) (Record toVars) ret

type VIxSTREff
  (realm :: Type)
  (eff :: # Effect)
  (fromVars :: # Type)
  (toVars :: # Type)
  (r :: # Type)
  (m :: # Type)
  = VIxSTEff realm eff fromVars toVars (STRecord realm r m)

type STEff realm eff
  = Eff (st :: ST realm | eff)

type OnSTRecord realm eff r m a
  = STRecord realm r m -> STEff realm eff a

type MutSTRecord realm eff r r' m m'
  = OnSTRecord realm eff r m (STRecord realm r' m')

instance functorIxSTEff :: Functor (IxSTEff realm eff x x) where
  map = liftM1
instance applicativeIxSTEff :: Applicative (IxSTEff realm eff x x) where
  pure = ipure
instance applyIxSTEff :: Apply (IxSTEff realm eff x x) where
  apply = ap
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
  ipure = IxSTEff <<< curry Monad.pure

class IxMonad m <= IxMonadState m where
  iget :: forall i. m i i i
  iput :: forall i j. j -> m i j Unit

instance ixMonadStateIxSTEff :: IxMonadState (IxSTEff realm eff) where
  iget = St.get
  iput s = IxSTEff $ const $ pure $ Tuple unit s

imodify :: forall m i j. IxMonadState m => (i -> j) -> m i j Unit
imodify f = iget :>>= f >>> iput

igets :: forall m i a. IxMonadState m => (i -> a) -> m i i a
igets f = iget :>>= f >>> ipure

runIxSTEff ::
  forall realm from to eff ret.
  IxSTEff realm eff from to ret ->
  from -> STEff realm eff (Tuple ret to)
runIxSTEff (IxSTEff f) = f

runVIxSTEff ::
  forall realm fromVars toVars eff ret.
  VIxSTEff realm eff fromVars toVars ret ->
  Record fromVars -> STEff realm eff (Tuple ret (Record toVars))
runVIxSTEff (IxSTEff f) = f

vbind ::
  forall realm x y z eff a b.
        VIxSTEff realm eff x y   a  ->
  (a -> VIxSTEff realm eff   y z b) ->
        VIxSTEff realm eff x   z b
vbind = ibind

vpure ::
  forall realm vars eff a.
  a -> VIxSTEff realm eff vars vars a
vpure = ipure

vbindLift ::
  forall realm x y z eff a b.
  VIxSTEff realm eff x y a ->
  (a -> STEff realm eff b) ->
  VIxSTEff realm eff x y b
vbindLift start f = start :>>= f >>> vliftEff
infixl 1 vbindLift as :>>=/

vliftBind ::
  forall realm x y z eff a b.
  STEff realm eff a ->
  (a -> VIxSTEff realm eff x y b) ->
  VIxSTEff realm eff x y b
vliftBind start f = vliftEff start :>>= f
infixl 1 vliftBind as /:>>=

vliftEff ::
  forall realm vars eff ret.
  Eff (st :: ST realm | eff) ret ->
  VIxSTEff realm eff vars vars ret
vliftEff = liftEff

pureVIxSTEff ::
  forall realm vars vars' eff ret.
  (Record vars -> Tuple ret (Record vars')) ->
  VIxSTEff realm eff vars vars' ret
pureVIxSTEff f = IxSTEff (pure <<< f)

withVIxSTEff ::
  forall realm vars eff ret.
  (Record vars -> ret) ->
  VIxSTEff realm eff vars vars ret
withVIxSTEff f =
  pureVIxSTEff \vars -> Tuple (f vars) vars

mapVIxSTEff ::
  forall realm vars vars' eff ret.
  (Record vars -> Record vars') ->
  VIxSTEff realm eff vars vars ret ->
  VIxSTEff realm eff vars vars' ret
mapVIxSTEff f start =
  start :>>= \v -> pureVIxSTEff (Tuple v <<< f)

getV ::
  forall name realm meh vars eff r m.
    IsSymbol name =>
    RowCons name (STRecord realm r m) meh vars =>
  SProxy name ->
  VIxSTREff realm eff vars vars r m
getV name =
  igets $ R.get name

setV ::
  forall name realm vars meh vars' eff r r' m.
    IsSymbol name =>
    RowCons name (STRecord realm r m) meh vars =>
    RowCons name (STRecord realm r' m) meh vars' =>
  SProxy name ->
  STRecord realm r' m ->
  VIxSTEff realm eff vars vars' Unit
setV name entry =
  imodify $ R.set name entry

insertV ::
  forall name realm vars vars' eff r m.
    IsSymbol name =>
    RowLacks name vars =>
    RowCons name (STRecord realm r m) vars vars' =>
  SProxy name ->
  STRecord realm r m ->
  VIxSTEff realm eff vars vars' Unit
insertV name entry =
  imodify $ R.insert name entry

modifyV ::
  forall name realm vars meh vars' eff r r' m.
    IsSymbol name =>
    RowCons name (STRecord realm r m) meh vars =>
    RowCons name (STRecord realm r' m) meh vars' =>
  SProxy name ->
  (STRecord realm r m -> Eff (st :: ST realm | eff) (STRecord realm r' m)) ->
  VIxSTEff realm eff vars vars' Unit
modifyV name f =
  getV name :>>=/ f :>>= setV name

thawAs ::
  forall name vars vars' realm r eff.
    IsSymbol name =>
    RowLacks name vars =>
    RowCons name (STRecord realm r ()) vars vars' =>
  SProxy name -> Record r ->
  VIxSTEff realm eff vars vars' Unit
thawAs name r =
  rawCopy r /:>>= insertV name

freezeFrom ::
  forall name meh vars realm r eff.
    IsSymbol name =>
    RowCons name (STRecord realm r ()) meh vars =>
  SProxy name ->
  VIxSTEff realm eff vars vars (Record r)
freezeFrom name =
  getV name :>>=/ rawCopy

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
  VIxSTEff realm eff vars vars t
get name k =
  getV name :>>=/ unmanagedGet k

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
  VIxSTEff realm eff vars vars Boolean
test name k =
  getV name :>>=/ unmanagedTest k

unmanagedGetM ::
  forall sym t r m m' realm eff f.
    Alternative f =>
    IsSymbol sym =>
    RowCons sym t m' m =>
  SProxy sym ->
  OnSTRecord realm eff r m (f t)
unmanagedGetM s r =
  let k = reflectSymbol s in
  ifM (not <$> rawExists k r) (pure empty)
    $ pure <$> rawGet k r

getM ::
  forall name sym t r m m' realm meh vars eff f.
    Alternative f =>
    IsSymbol name =>
    IsSymbol sym =>
    RowCons sym t m' m =>
    RowCons name (STRecord realm r m) meh vars =>
  SProxy name -> SProxy sym ->
  VIxSTEff realm eff vars vars (f t)
getM name k =
  getV name :>>=/ unmanagedGetM k

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
  t -> VIxSTEff realm eff vars vars' Unit
insert name k v =
  modifyV name $ unmanagedInsert k v

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
  VIxSTEff realm eff vars vars' Unit
delete name k =
  modifyV name $ unmanagedDelete k
