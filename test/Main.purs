module Test.Main where

import Data.Record.ST

import Control.IxMonad (ipure, (:*>), (:>>=))
import Control.IxMonad.State.IxSTEff (IxSTEff(..))
import Control.IxMonad.State.MVIxSTEff (MVIxSTEff, getV, mvliftEff, (:>>=/))
import Control.Monad.Eff (Eff)
import Control.Monad.Eff.Console (CONSOLE)
import Control.Monad.ST (runST)
import Data.Maybe (Maybe(..), fromMaybe, maybe)
import Data.Record.ST.Operations (freezeMaybesFrom)
import Data.Symbol (class IsSymbol, SProxy(..), reflectSymbol)
import Data.Tuple (fst)
import Prelude (class Eq, class Show, Unit, add, const, eq, map, show, unit, (<<<), (<>), (==))
import Test.Assert (ASSERT, assert')
import Type.Row (class RowLacks)

assertlifted :: forall realm eff vars.
  String -> Boolean ->
  MVIxSTEff realm ( assert :: ASSERT | eff ) vars vars Unit
assertlifted m c = mvliftEff (assert' m c)

asserteq ::
  forall name key value realm e r r' m meh vars.
    IsSymbol name =>
    IsSymbol key =>
    Show value =>
    Eq value =>
    RowCons key value r' r =>
    RowLacks key m =>
    RowCons name (STRecord realm r m) meh vars =>
  SProxy name -> SProxy key -> value ->
  MVIxSTEff realm ( assert :: ASSERT | e ) vars vars Unit
asserteq name key v =
  let
    n = reflectSymbol name
    k = reflectSymbol key
    assertion actual = n <> "." <> k <> " should equal " <> show v <> " but it was " <> show actual
  in getV name :>>=/ unmanagedGet key :>>=/ \actual ->
    assert' (assertion actual) (v == actual)

asserteqife ::
  forall name key value realm e r m' m meh vars.
    IsSymbol name =>
    IsSymbol key =>
    Show value =>
    Eq value =>
    RowLacks key r =>
    RowCons key value m' m =>
    RowCons name (STRecord realm r m) meh vars =>
  SProxy name -> SProxy key -> value ->
  MVIxSTEff realm ( assert :: ASSERT | e ) vars vars Unit
asserteqife name key v =
  let
    n = reflectSymbol name
    k = reflectSymbol key
    assertion actual = n <> "." <> k <> " should equal " <> show v <> " but it was " <> show actual
  in getV name :>>=/ unmanagedGetM key :>>=/ \actual ->
    assert' (assertion actual) (maybe true (eq v) actual)

runIX :: forall e vs ret. (forall realm. VIxSTEff realm e () vs ret) -> Eff e ret
runIX (IxSTEff f) = (map fst (runST (f {})))

main :: forall eff. Eff (console :: CONSOLE, assert :: ASSERT | eff) Unit
main =
  let
    ainit = { a: 1 }
    a = SProxy :: SProxy "a"
    b = SProxy :: SProxy "b"
  in runIX (
    thawAs a ainit :*>
    asserteq a a 1 :*>
    freezeFrom a :>>= \acopy1 ->
    delete a a :*>
    insert a a "hi" :*>
    asserteq a a "hi" :*>
    assertlifted "ainit.a == 1" (ainit.a == 1) :*>
    assertlifted "acopy1.a == 1" (acopy1.a == 1) :*>
    insertM a b false 2 :*>
    freezeMaybesFrom a :>>= \acopy2 ->
    alter a b (Just <<< maybe 3 (add 5)) :*>
    asserteqife a b 3 :*>
    assertlifted "acopy2.b == Nothing" (acopy2.b == Nothing) :*>
    freezeMaybesFrom a :>>= \acopy3 ->
    alter a b (Just <<< maybe 3 (add 5)) :*>
    asserteqife a b 8 :*>
    assertlifted "acopy3.b == Just 3" (acopy3.b == Just 3) :*>
    alter a b (const (Nothing :: Maybe Int)) :*>
    ensure a b (fromMaybe 5 :: Maybe Int -> Int) :*>
    asserteq a b 5 :*>
    freezeFrom a :>>= \acopy4 ->
    assertlifted "acopy4.a == \"hi\"" (acopy4.a == "hi") :*>
    assertlifted "acopy4.b == 5" (acopy4.b == 5) :*>
    assertlifted "acopy1.a == 1" (acopy1.a == 1) :*>
    unsafeFreeze a :>>= \mutablea ->
    ipure unit
  )
