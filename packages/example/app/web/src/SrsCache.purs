-- | The browser SRS cache backend: an `SrsCache` over IndexedDB. BROWSER ONLY —
-- | its FFI uses `indexedDB`. IndexedDB is shared across all same-origin
-- | contexts, so the engine worker and the nested self-prover worker open the
-- | SAME database: whichever builds the SRS first warms it for the other (no
-- | postMessage transfer of the bases needed), and the cache survives reloads.
module Snarky.Example.Web.SrsCache
  ( idbSrsCache
  ) where

import Prelude

import Control.Promise (Promise, toAffE)
import Data.ArrayBuffer.Types (Uint8Array)
import Data.Maybe (Maybe(..))
import Data.Nullable (Nullable, toMaybe)
import Effect (Effect)
import Effect.Aff (Aff)
import Fmt (fmt)
import Snarky.Example.Log (Logger)
import Snarky.Example.Log as Log
import Snarky.Example.Srs.Cache (SrsCache, entryKey)

-- | The shared same-origin database name used by every prover in the app.
srsCacheDb :: String
srsCacheDb = "snarky-srs-cache"

foreign import data IdbDb :: Type

foreign import _open :: String -> Effect (Promise IdbDb)
foreign import _get :: IdbDb -> String -> Effect (Promise (Nullable Uint8Array))
foreign import _put :: IdbDb -> String -> Uint8Array -> Effect (Promise Unit)

-- | Open (creating the object store on first use) and return an `SrsCache`.
idbCache :: String -> Aff SrsCache
idbCache name = do
  db <- toAffE (_open name)
  pure
    { get: \e -> toMaybe <$> toAffE (_get db (entryKey e))
    , put: \e bytes -> toAffE (_put db (entryKey e) bytes)
    }

-- | Wrap an `SrsCache` so every lookup logs HIT (loaded + injected, no FFT) or
-- | MISS (will build + store) per entry — same decorator as the terminal, kept
-- | app-side so the cache manager stays silent.
loggingCache :: Logger -> SrsCache -> SrsCache
loggingCache logger inner = inner
  { get = \e -> do
      result <- inner.get e
      Log.logInfo logger $ case result of
        Just _ -> fmt @"[srs-cache] hit {key} (reused, no FFT)" { key: entryKey e }
        Nothing -> fmt @"[srs-cache] miss {key} (building + storing)" { key: entryKey e }
      pure result
  }

-- | Open the shared IndexedDB SRS cache with hit/miss logging.
idbSrsCache :: Logger -> Aff SrsCache
idbSrsCache logger = loggingCache logger <$> idbCache srsCacheDb
