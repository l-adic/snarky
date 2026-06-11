-- | Function-local mutable dense stores (Int-indexed) for the constraint-
-- | system wiring passes: an `STArray h (Maybe v)`. Region-quantified —
-- | callers wrap create→fill→read in `ST.run`, which proves the mutation
-- | is local and keeps the passes pure with no unsafe operations.
module Snarky.Backend.DenseStore
  ( DenseStore
  , fresh
  , pushAt
  , setAt
  , toEntries
  , freeze
  ) where

import Prelude

import Control.Monad.ST (ST)
import Control.Monad.ST.Internal (for) as STI
import Data.Array as Array
import Data.Array.ST (STArray)
import Data.Array.ST as STA
import Data.FunctorWithIndex (mapWithIndex)
import Data.Maybe (Maybe(..))

newtype DenseStore h v = DenseStore (STArray h (Maybe v))

fresh :: forall h v. ST h (DenseStore h v)
fresh = DenseStore <$> STA.new

-- | Poke with `Nothing`-padding growth to cover sparse indices.
write :: forall h v. Int -> Maybe v -> STArray h (Maybe v) -> ST h Unit
write i v s = do
  n <- Array.length <$> STA.unsafeFreeze s
  STI.for n (i + 1) (\_ -> STA.push Nothing s)
  void (STA.poke i v s)

-- | Append `v` to the array at slot `i`.
pushAt :: forall h v. Int -> v -> DenseStore h (Array v) -> ST h Unit
pushAt i v (DenseStore s) = do
  cur <- STA.peek i s
  case join cur of
    Just xs -> write i (Just (Array.snoc xs v)) s
    Nothing -> write i (Just [ v ]) s

setAt :: forall h v. Int -> v -> DenseStore h v -> ST h Unit
setAt i v (DenseStore s) = write i (Just v) s

-- | Frozen copy of all slots.
freeze :: forall h v. DenseStore h v -> ST h (Array (Maybe v))
freeze (DenseStore s) = STA.freeze s

-- | All filled slots, ascending by index.
toEntries :: forall h v r. (Int -> v -> r) -> DenseStore h v -> ST h (Array r)
toEntries mk (DenseStore s) =
  STA.freeze s <#> \arr -> Array.catMaybes (mapWithIndex (\i -> map (mk i)) arr)
