module Data.Record.ST.Operations where

import Prelude

import Control.Bind (bindFlipped)
import Control.IxMonad.State.MVIxSTEff (getV, (:>>=/))
import Data.Maybe (Maybe)
import Data.Record.ST (MutSTRecord, STRecord, VIxSTEff, rawCopy, unmanagedEnsure)
import Data.Symbol (class IsSymbol, SProxy(..))
import Type.Row (class ListToRow, class RowLacks, class RowToList, Cons, Nil, RLProxy(..), kind RowList)
import Unsafe.Coerce (unsafeCoerce)

class FreezeMaybes
  (rl :: RowList)
  (ml :: RowList)
  (rl' :: RowList)
  (r :: # Type)
  (m :: # Type)
  (r' :: # Type)
  | ml -> rl rl' r m r'
  where
    freezeMaybes' :: forall realm eff.
      RLProxy rl -> RLProxy ml -> RLProxy rl' ->
      MutSTRecord realm eff r r' m ()

instance freezeNil ::
  ( ListToRow rl r
  ) => FreezeMaybes rl Nil rl r () r
  where
  freezeMaybes' _ _ _ = pure

instance freezeCons ::
    -- get the key
  ( IsSymbol sym
    -- remove the key from m to create intermediate m_ (handled by subinstance)
  , RowCons sym t m_ m
  , RowLacks sym m_
    -- and add the key to r_, also passed to subinstance
  , RowLacks sym r
  , RowCons sym (Maybe t) r r_
    -- the key should appear in the result
  , RowCons sym (Maybe t) __ r'
  , ListToRow (Cons sym (Maybe t) rl') r'
  , FreezeMaybes (Cons sym (Maybe t) rl) ml (Cons sym (Maybe t) rl') r_ m_ r'
  ) => FreezeMaybes rl (Cons sym t ml) (Cons sym (Maybe t) rl') r m r'
  where
    freezeMaybes' :: forall realm eff.
      RLProxy rl -> RLProxy (Cons sym t ml) -> RLProxy (Cons sym (Maybe t) rl') ->
      MutSTRecord realm eff r r' m ()
    freezeMaybes' _ _ _ = ens >>> bindFlipped fzM
      where
        -- ens :: MutSTRecord _ _ r r_ m m_
        ens = unmanagedEnsure (SProxy :: SProxy sym) id
        -- fzM :: MutSTRecord _ _ r_ r' m_ ()
        fzM = freezeMaybes' (RLProxy :: RLProxy (Cons sym (Maybe t) rl)) (RLProxy :: RLProxy ml) (RLProxy :: RLProxy (Cons sym (Maybe t) rl'))

freezeMaybesFrom :: forall name meh vars realm eff r r' m rl ml rl'.
    IsSymbol name =>
    RowToList r rl =>
    RowToList m ml =>
    ListToRow rl' r' =>
    FreezeMaybes rl ml rl' r m r' =>
    RowCons name (STRecord realm r m) meh vars =>
  SProxy name ->
  VIxSTEff realm eff vars vars (Record r')
freezeMaybesFrom name = getV name :>>=/ rawCopy :>>=/ freezeMaybes'
  (RLProxy :: RLProxy rl) (RLProxy :: RLProxy ml) (RLProxy :: RLProxy rl')
  <#> (unsafeCoerce :: STRecord realm r' () -> Record r')
