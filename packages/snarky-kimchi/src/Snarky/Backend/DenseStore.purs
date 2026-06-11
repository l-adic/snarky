-- | Function-local mutable dense stores (Int-indexed) for the constraint-
-- | system wiring passes: an `STArray h (Maybe v)`. Region-quantified —
-- | callers wrap create→fill→read in `ST.run`, which proves the mutation
-- | is local and keeps the passes pure with no unsafe operations.
module Snarky.Backend.DenseStore
  ( DenseStore
  , fresh
  , pushAt
  , setAt
  , getAt
  , foldSlots
  , toEntries
  , freeze
  ) where

import Prelude

import Control.Monad.ST (ST)
import Data.Array as Array
import Data.Array.ST (STArray)
import Data.Array.ST as STA
import Data.FoldableWithIndex (foldlWithIndex)
import Data.FunctorWithIndex (mapWithIndex)
import Data.Maybe (Maybe(..))

newtype DenseStore h v = DenseStore (STArray h (Maybe v))

fresh :: forall h v. ST h (DenseStore h v)
fresh = DenseStore <$> STA.new

-- | Poke with `Nothing`-padding growth to cover sparse indices.
write :: forall h v. Int -> Maybe v -> STArray h (Maybe v) -> ST h Unit
write i v s = do
  ok <- STA.poke i v s
  if ok then pure unit
  else do
    _ <- STA.push Nothing s
    write i v s

-- | Append `v` to the array at slot `i`.
pushAt :: forall h v. Int -> v -> DenseStore h (Array v) -> ST h Unit
pushAt i v (DenseStore s) = do
  cur <- STA.peek i s
  case join cur of
    Just xs -> write i (Just (Array.snoc xs v)) s
    Nothing -> write i (Just [ v ]) s

setAt :: forall h v. Int -> v -> DenseStore h v -> ST h Unit
setAt i v (DenseStore s) = write i (Just v) s

getAt :: forall h v. Int -> DenseStore h v -> ST h (Maybe v)
getAt i (DenseStore s) = join <$> STA.peek i s

-- | Fold filled slots, ascending by index (freezes a snapshot).
foldSlots :: forall h v r. (r -> Int -> v -> r) -> r -> DenseStore h v -> ST h r
foldSlots f init (DenseStore s) =
  STA.freeze s <#> foldlWithIndex
    ( \i acc -> case _ of
        Just v -> f acc i v
        Nothing -> acc
    )
    init

-- | Frozen snapshot of all slots.
freeze :: forall h v. DenseStore h v -> ST h (Array (Maybe v))
freeze (DenseStore s) = STA.freeze s

-- | All filled slots, ascending by index.
toEntries :: forall h v r. (Int -> v -> r) -> DenseStore h v -> ST h (Array r)
toEntries mk (DenseStore s) =
  STA.freeze s <#> \arr -> Array.catMaybes (mapWithIndex (\i -> map (mk i)) arr)
