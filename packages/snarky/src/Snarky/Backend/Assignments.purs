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
  , Frozen
  , fresh
  , set
  , lookup
  , freeze
  , lookupFrozen
  , toLookup
  ) where

import Prelude

import Control.Monad.ST.Global (Global, toEffect)
import Control.Monad.ST.Internal (for) as STI
import Data.Array as Array
import Data.Array.ST (STArray)
import Data.Array.ST as STA
import Data.Maybe (Maybe(..))
import Effect (Effect)
import Effect.Unsafe (unsafePerformEffect)
import Snarky.Circuit.CVar (Variable(..))

newtype Assignments f = Assignments (STArray Global (Maybe f))

fresh :: forall f. Effect (Assignments f)
fresh = Assignments <$> toEffect STA.new

-- | Write a slot (write-once). Mostly-sequential — variables allocate in
-- | order, but output slots are back-filled by `Assign` — so: grow with
-- | `Nothing` padding to cover the index, then poke.
set :: forall f. Variable -> f -> Assignments f -> Effect Unit
set (Variable i) v (Assignments s) =
  toEffect do
    n <- Array.length <$> STA.unsafeFreeze s
    STI.for n (i + 1) (\_ -> STA.push Nothing s)
    void (STA.poke i (Just v) s)

-- | Pure read of the mutable store — the branch's single sanctioned
-- | `unsafePerformEffect`.
-- |
-- | CONTRACT (what makes this observationally pure): slots are write-once —
-- | each is written exactly once, when its variable is allocated — and no
-- | read targets a slot before that write. A successful lookup is therefore
-- | referentially stable forever.
-- |
-- | MEASUREMENT (why the escape hatch earns its keep): routing these reads
-- | through `Run.liftEffect` instead costs ~+40% prove js/rust ratio
-- | (1.77 -> 2.48) and +45% allocation (32GB -> 47GB reclaim/prove) — one
-- | Free node + Effect thunk per witness read, millions per prove
-- | (bench artifacts a34dffc87-2026-06-11T19-42 vs the f5400db8f family).
lookup :: forall f. Variable -> Assignments f -> Maybe f
lookup (Variable i) (Assignments s) = join (unsafePerformEffect (toEffect (STA.peek i s)))

-- | Immutable end-of-solve snapshot of the store. `Variable` is a dense
-- | integer index, so this IS the final lookup structure — O(n) to copy
-- | once, O(1) per lookup, no tree to build or walk.
newtype Frozen f = Frozen (Array (Maybe f))

-- | Snapshot the store (one array copy).
freeze :: forall f. Assignments f -> Effect (Frozen f)
freeze (Assignments s) = Frozen <$> toEffect (STA.freeze s)

-- | O(1) read of a snapshot. `Nothing` for out-of-range or never-assigned
-- | variables alike.
lookupFrozen :: forall f. Variable -> Frozen f -> Maybe f
lookupFrozen (Variable i) (Frozen arr) = join (Array.index arr i)

-- | Pure lookup over a frozen snapshot — for consumers that need a
-- | `Variable -> Maybe f` function (debug checks, error formatting).
toLookup :: forall f. Assignments f -> Effect (Variable -> Maybe f)
toLookup s = freeze s <#> flip lookupFrozen
