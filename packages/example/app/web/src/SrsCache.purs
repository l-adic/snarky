-- | The browser app's Lagrange cache: the shared IndexedDB backend
-- | (`Snarky.Lagrange.Cache.Idb`) wrapped with hit/miss logging at DEBUG, so the
-- | default info-level coordinator/worker views stay clean while the per-entry
-- | detail is still available under debug logging. IndexedDB is shared across all
-- | same-origin contexts, so the engine worker and the nested self-prover worker
-- | open the SAME database and warm it for each other.
module Snarky.Example.Web.SrsCache
  ( idbLagrangeCache
  ) where

import Prelude

import Effect.Aff (Aff)
import Snarky.Example.Log (Logger)
import Snarky.Example.Log as Log
import Snarky.Lagrange.Cache (LagrangeCache, loggingCache)
import Snarky.Lagrange.Cache.Idb (defaultDb, idbCache)

-- | Open the shared IndexedDB Lagrange cache with debug-level hit/miss logging.
idbLagrangeCache :: Logger -> Aff LagrangeCache
idbLagrangeCache logger = loggingCache (Log.logDebug logger) <$> idbCache defaultDb
