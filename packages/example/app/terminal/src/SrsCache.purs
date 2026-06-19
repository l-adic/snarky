-- | The node terminal's shared SRS cache: one on-disk directory (under tmp, or
-- | `SNARK_SRS_CACHE_DIR`) that the host simulation process AND every worker
-- | thread build through, so the Lagrange-basis FFTs run once across the whole
-- | run (and persist across runs). The logging decorator surfaces each lookup
-- | as a HIT/MISS line; it lives here in the app, so the cache manager
-- | (`Snarky.Example.Srs.Cache`) stays silent — the `{ get, put }` seam carries
-- | the observability.
module Snarky.Example.Terminal.SrsCache
  ( resolveSrsCacheDir
  , loggingCache
  , openSrsCache
  ) where

import Prelude

import Data.Maybe (Maybe(..))
import Effect (Effect)
import Fmt (fmt)
import Snarky.Example.Log (Logger)
import Snarky.Example.Log as Log
import Snarky.Example.Srs.Cache (SrsCache, entryKey)
import Snarky.Example.Srs.Cache.Fs (fsCache)

-- | The on-disk SRS cache directory shared by the host + all worker threads (and
-- | reused across runs); `SNARK_SRS_CACHE_DIR` overrides it.
foreign import resolveSrsCacheDir :: Effect String

-- | Wrap an `SrsCache` so every lookup logs HIT (loaded + injected, no FFT) or
-- | MISS (will build + store) per entry.
loggingCache :: Logger -> SrsCache -> SrsCache
loggingCache logger inner = inner
  { get = \e -> do
      result <- inner.get e
      Log.logInfo logger $ case result of
        Just _ -> fmt @"[srs-cache] hit {key} (reused, no FFT)" { key: entryKey e }
        Nothing -> fmt @"[srs-cache] miss {key} (building + storing)" { key: entryKey e }
      pure result
  }

-- | Open the shared on-disk SRS cache with hit/miss logging.
openSrsCache :: Logger -> Effect SrsCache
openSrsCache logger = loggingCache logger <<< fsCache <$> resolveSrsCacheDir
