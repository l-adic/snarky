-- | The browser `LagrangeCache` over IndexedDB. BROWSER ONLY — its FFI uses
-- | `indexedDB`. IndexedDB is shared (and concurrent-safe) across all same-origin
-- | contexts, so the engine worker and the nested self-prover worker share one
-- | store; whichever computes a basis first warms it for the other, and it
-- | survives reloads.
-- |
-- | IndexedDB has no synchronous API, so this serves the synchronous
-- | `LagrangeCache` via `Snarky.Lagrange.Cache.Hydrated`: bulk-load the store
-- | into an in-memory map once (`getAll`), serve `get`/`put` off the map, and
-- | persist each `put` back to IndexedDB fire-and-forget.
module Snarky.Lagrange.Cache.Idb
  ( idbCache
  , defaultDb
  ) where

import Prelude

import Control.Promise (Promise, toAffE)
import Data.Array (zip)
import Data.ArrayBuffer.Types (Uint8Array)
import Data.Map as Map
import Effect (Effect)
import Effect.Aff (Aff)
import Snarky.Lagrange.Cache (LagrangeCache)
import Snarky.Lagrange.Cache.Hydrated (hydratedCache)

-- | The shared same-origin database name used by every prover in the app.
defaultDb :: String
defaultDb = "snarky-lagrange-cache"

foreign import data IdbDb :: Type

foreign import _open :: String -> Effect (Promise IdbDb)
foreign import _put :: IdbDb -> String -> Uint8Array -> Effect (Promise Unit)
foreign import _getAll :: IdbDb -> Effect (Promise { keys :: Array String, values :: Array Uint8Array })

-- | Open the store (creating it on first use), hydrate from it, and return a
-- | synchronous cache whose `put` persists back fire-and-forget.
idbCache :: String -> Aff LagrangeCache
idbCache name = do
  db <- toAffE (_open name)
  hydratedCache
    { loadAll: toAffE (_getAll db) <#> \{ keys, values } -> Map.fromFoldable (zip keys values)
    , putAsync: \key bytes -> toAffE (_put db key bytes)
    }
