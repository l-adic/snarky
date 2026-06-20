-- | The node terminal app's Lagrange cache: the shared on-disk backend
-- | (`Snarky.Lagrange.Cache.FS`, default dir or `SNARK_LAGRANGE_CACHE_DIR`)
-- | wrapped with hit/miss logging at DEBUG. Every worker thread warms through
-- | this one directory, so each Lagrange-basis FFT runs once across the whole run
-- | and persists across runs. Logging at debug keeps the default info view clean.
module Snarky.Example.Terminal.SrsCache
  ( fsLagrangeCache
  ) where

import Prelude

import Effect (Effect)
import Snarky.Example.Log (Logger)
import Snarky.Example.Log as Log
import Snarky.Lagrange.Cache (LagrangeCache, loggingCache)
import Snarky.Lagrange.Cache.FS (defaultDir, fsCache)

-- | Open the shared on-disk Lagrange cache with debug-level hit/miss logging.
fsLagrangeCache :: Logger -> Effect LagrangeCache
fsLagrangeCache logger = loggingCache (Log.logDebug logger) <<< fsCache <$> defaultDir
