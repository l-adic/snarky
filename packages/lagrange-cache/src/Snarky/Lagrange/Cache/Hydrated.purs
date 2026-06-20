-- | A synchronous `LagrangeCache` backed by an in-memory map hydrated once
-- | (asynchronously) from a durable store, writing back fire-and-forget. This
-- | lets an async-only backend — chiefly browser IndexedDB, whose API has no
-- | synchronous variant — feed the synchronous compile-time warm.
-- |
-- | The map is the session's source of truth: `get`/`put` are synchronous, so an
-- | in-session read always sees what was just `put` (the durable write is
-- | irrelevant to it). The durable store is eventually-consistent — a `put`
-- | updates the map immediately and kicks off the async write in the background.
-- | A different context reading the durable store before that write lands simply
-- | misses and recomputes (bases are deterministic — a wasted FFT at worst,
-- | never a wrong value).
module Snarky.Lagrange.Cache.Hydrated
  ( DurableStore
  , hydratedCache
  ) where

import Prelude

import Data.ArrayBuffer.Types (Uint8Array)
import Data.Map (Map)
import Data.Map as Map
import Effect.Aff (Aff, launchAff_)
import Effect.Class (liftEffect)
import Effect.Ref as Ref
import Snarky.Lagrange.Cache (LagrangeCache, keyString)

-- | The async durable backing: bulk-load everything stored (to hydrate the map
-- | up front, since a synchronous `get` cannot fetch on miss), and persist one
-- | entry (run fire-and-forget on `put`). Keyed by `keyString`.
type DurableStore =
  { loadAll :: Aff (Map String Uint8Array)
  , putAsync :: String -> Uint8Array -> Aff Unit
  }

-- | Hydrate an in-memory map from `store` and return a synchronous cache over it
-- | whose `put` also persists back to `store` fire-and-forget.
hydratedCache :: DurableStore -> Aff LagrangeCache
hydratedCache store = do
  initial <- store.loadAll
  ref <- liftEffect (Ref.new initial)
  pure
    { get: \k -> Map.lookup (keyString k) <$> Ref.read ref
    , put: \k bytes -> do
        Ref.modify_ (Map.insert (keyString k) bytes) ref
        launchAff_ (store.putAsync (keyString k) bytes)
    }
