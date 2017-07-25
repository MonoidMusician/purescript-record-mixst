module Data.Record.ST where

import Control.Monad as Monad
import Control.Monad.Eff (Eff, kind Effect)
import Control.Monad.ST (ST)
import Control.Plus (empty)
import Data.Maybe (Maybe(..))
import Data.Record as R
import Data.Tuple (Tuple(..), curry, uncurry)
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

type STEff
  (realm :: Type)
  (fromVars :: # Type)
  (toVars :: # Type)
  (eff :: # Effect)
  (ret :: Type)
  = Record fromVars -> Eff (st :: ST realm | eff) (Tuple ret (Record toVars))
type STREff
  (realm :: Type)
  (fromVars :: # Type)
  (toVars :: # Type)
  (eff :: # Effect)
  (r :: # Type)
  (m :: # Type)
  = STEff realm fromVars toVars eff (STRecord realm r m)

rbind ::
  forall realm x y z eff a b.
        STEff realm x y   eff a ->
  (a -> STEff realm   y z eff b) ->
        STEff realm x   z eff b
rbind start next vars = start vars >>= uncurry next
infixl 1 rbind as >>~

rpure ::
  forall realm vars eff a.
  a -> STEff realm vars vars eff a
rpure = curry Monad.pure

rliftEff ::
  forall realm vars eff ret.
  Eff (st :: ST realm | eff) ret -> STEff realm vars vars eff ret
rliftEff e vars = e <#> flip Tuple vars

rget ::
  forall name realm meh vars eff r m.
    IsSymbol name =>
    RowCons name (STRecord realm r m) meh vars =>
  SProxy name -> STREff realm vars vars eff r m
rget name vars = pure (Tuple (R.get name vars) vars)

rput ::
  forall name r r' realm vars meh vars' eff r m.
    IsSymbol name =>
    RowCons name (STRecord realm r m) meh vars =>
    RowCons name (STRecord realm r' m) meh vars' =>
  SProxy name -> STRecord realm r' m -> STEff realm vars vars' eff Unit
rput name entry vars = pure (Tuple unit (R.set name entry vars))

thawAs ::
  forall name vars vars' realm r eff.
    IsSymbol name =>
    RowLacks name vars =>
    RowCons name (STRecord realm r ()) vars vars' =>
  SProxy name -> Record r ->
  STEff realm vars vars' eff Unit
thawAs name r vars = rawCopy r <#> \entry ->
  Tuple unit (R.insert name entry vars)

foreign import rawCopy ::
  forall a b realm eff.
  a -> Eff (st :: ST realm | eff) b
foreign import rawExists ::
  forall r m realm eff.
  String -> STRecord realm r m -> Eff (st :: ST realm | eff) Boolean
foreign import rawGet ::
  forall r m b realm eff.
  String -> STRecord realm r m -> Eff (st :: ST realm | eff) b
foreign import rawSet ::
  forall r m v realm eff.
  String -> v -> STRecord realm r m -> Eff (st :: ST realm | eff) Unit

unmanagedGet ::
  forall sym t r r' m realm vars eff.
    IsSymbol sym =>
    RowCons sym t r' r =>
  SProxy sym -> STRecord realm r m -> STEff realm vars vars eff t
unmanagedGet k r = rliftEff (rawGet (reflectSymbol k) r)

get ::
  forall name sym t r r' m realm meh vars eff.
    IsSymbol name =>
    IsSymbol sym =>
    RowCons sym t r' r =>
    RowCons name (STRecord realm r m) meh vars =>
  SProxy name -> SProxy sym -> STEff realm vars vars eff t
get name k = rget name >>~ unmanagedGet k

unmanagedTest ::
  forall sym t r m m' realm vars eff.
    IsSymbol sym =>
    RowCons sym t m' m =>
  SProxy sym -> STRecord realm r m -> STEff realm vars vars eff Boolean
unmanagedTest k = rliftEff <<< rawExists (reflectSymbol k)

test ::
  forall name sym t r m m' realm meh vars eff.
    IsSymbol name =>
    IsSymbol sym =>
    RowCons sym t m' m =>
    RowCons name (STRecord realm r m) meh vars =>
  SProxy name -> SProxy sym -> STEff realm vars vars eff Boolean
test name k = rget name >>~ unmanagedTest k

unmanagedGetM ::
  forall sym t r m m' realm vars eff.
    IsSymbol sym =>
    RowCons sym t m' m =>
  SProxy sym -> STRecord realm r m -> STEff realm vars vars eff (Maybe t)
unmanagedGetM s r =
  let k = reflectSymbol s
  in rliftEff $ rawExists k r >>=
    if _
      then Just <$> rawGet k r
      else pure empty

getM ::
  forall name sym t r m m' realm meh vars eff.
    IsSymbol name =>
    IsSymbol sym =>
    RowCons sym t m' m =>
    RowCons name (STRecord realm r m) meh vars =>
  SProxy name -> SProxy sym -> STEff realm vars vars eff (Maybe t)
getM name k = rget name >>~ unmanagedGetM k

unmanagedInsert ::
  forall sym t r r' m realm eff.
    IsSymbol sym =>
    RowLacks sym r =>
    RowCons sym t r r' =>
  SProxy sym -> t -> STRecord realm r m -> Eff (st :: ST realm | eff) (STRecord realm r' m)
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
  SProxy name -> SProxy sym -> t -> STEff realm vars vars' eff Unit
insert name k v = let bind = rbind in do
  entry <- rget name
  entry' <- rliftEff $ unmanagedInsert k v entry
  rput name entry'
