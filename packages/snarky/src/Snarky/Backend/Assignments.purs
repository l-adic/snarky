-- | Dense mutable assignment store for the prover, indexed by `Variable`'s
-- | underlying `Int`. Replaces `Map Variable f`: O(1) write-once inserts and
-- | O(1) witness lookups with zero allocation, versus the Map's O(log n)
-- | path-copying on both (the dominant state-structure garbage of a prove).
-- |
-- | Writes live in `Effect` — the prover interpreter runs at
-- | `Run (EFFECT + r)` and owns one store per solver invocation. Reads are
-- | pure: slots are write-once (each is written exactly once, when its
-- | variable is allocated), so a successful `lookup` is stable forever.
module Snarky.Backend.Assignments
  ( Assignments
  , fresh
  , emptyFrozen
  , set
  , lookup
  , toMap
  ) where

import Prelude

import Data.Function.Uncurried (Fn3, Fn4, runFn3, runFn4)
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Effect (Effect)
import Snarky.Circuit.CVar (Variable(..))

foreign import data Assignments :: Type -> Type

-- | A new empty store.
foreign import fresh :: forall f. Effect (Assignments f)

-- | Immutable empty store for initial-state records (`emptyProverState`).
-- | The solver installs a `fresh` store before any write; writing to this
-- | placeholder throws (it is frozen), turning aliasing bugs into noise.
foreign import emptyFrozen :: forall f. Assignments f

foreign import setImpl :: forall f. Fn3 Int f (Assignments f) (Effect Unit)

foreign import lookupImpl :: forall f. Fn4 (f -> Maybe f) (Maybe f) Int (Assignments f) (Maybe f)

foreign import foldEntriesImpl :: forall f r. Fn3 (r -> Int -> f -> r) r (Assignments f) r

-- | Write a slot (write-once: each variable's slot is written exactly once,
-- | at its allocation).
set :: forall f. Variable -> f -> Assignments f -> Effect Unit
set (Variable i) v s = runFn3 setImpl i v s

lookup :: forall f. Variable -> Assignments f -> Maybe f
lookup (Variable i) s = runFn4 lookupImpl Just Nothing i s

-- | Materialise to the immutable `Map` the solver's consumers expect — one
-- | O(n log n) pass at the end of a solve, in exchange for O(1) everywhere
-- | the prover and witnesses touch assignments.
toMap :: forall f. Assignments f -> Map Variable f
toMap s = runFn3 foldEntriesImpl (\acc i v -> Map.insert (Variable i) v acc) Map.empty s
