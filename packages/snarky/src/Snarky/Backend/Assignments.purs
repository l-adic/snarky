-- | Dense mutable assignment store for the prover, indexed by `Variable`'s
-- | underlying `Int` — an `STArray Global` (variables allocate sequentially,
-- | so writes are appends). O(1) write-once inserts and O(1) witness lookups
-- | versus the old `Map`'s O(log n) path-copying on both.
-- |
-- | Writes live in `Effect` (via `toEffect`; `ST Global` and `Effect` share
-- | a runtime representation). Reads are pure: slots are write-once — each
-- | is written exactly once, when its variable is allocated — so a
-- | successful `lookup` is stable forever.
module Snarky.Backend.Assignments
  ( Assignments
  , fresh
  , emptyFrozen
  , set
  , lookup
  , toMap
  ) where

import Prelude

import Control.Monad.ST (ST) as ST
import Control.Monad.ST.Global (Global, toEffect)
import Data.Array.ST (STArray)
import Data.Array.ST as STA
import Data.FoldableWithIndex (foldlWithIndex)
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Effect (Effect)
import Effect.Unsafe (unsafePerformEffect)
import Snarky.Circuit.CVar (Variable(..))

newtype Assignments f = Assignments (STArray Global (Maybe f))

fresh :: forall f. Effect (Assignments f)
fresh = Assignments <$> toEffect STA.new

-- | Immutable empty store for initial-state records (`emptyProverState`).
-- | The solver installs a `fresh` store before any write; this placeholder
-- | must never be written.
emptyFrozen :: forall f. Assignments f
emptyFrozen = unsafePerformEffect fresh

-- | Write a slot (write-once). Mostly-sequential — variables allocate in
-- | order, but output slots are back-filled by `Assign` — so: grow with
-- | `Nothing` padding to cover the index, then poke.
set :: forall f. Variable -> f -> Assignments f -> Effect Unit
set (Variable i) v (Assignments s) = toEffect (grow unit)
  where
  grow :: Unit -> ST.ST Global Unit
  grow _ = do
    ok <- STA.poke i (Just v) s
    if ok then pure unit
    else do
      _ <- STA.push Nothing s
      grow unit

lookup :: forall f. Variable -> Assignments f -> Maybe f
lookup (Variable i) (Assignments s) = join (unsafePerformEffect (toEffect (STA.peek i s)))

-- | Materialise to the immutable `Map` the solver's consumers expect — one
-- | O(n log n) pass at the end of a solve.
toMap :: forall f. Assignments f -> Effect (Map Variable f)
toMap (Assignments s) = toEffect $ STA.freeze s <#> foldlWithIndex
  ( \i acc -> case _ of
      Just v -> Map.insert (Variable i) v acc
      Nothing -> acc
  )
  Map.empty
