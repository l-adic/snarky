-- | A filesystem-backed `SrsCache` for the Node runtime (the terminal app and
-- | Node simulations): one file per `SrsEntry` under a directory, so the SRS
-- | generators + Lagrange bases survive across process runs. NODE ONLY — its FFI
-- | imports `node:fs/promises`; the browser uses `Snarky.Example.Srs.Cache.Idb`
-- | instead, and never imports this module.
module Snarky.Example.Srs.Cache.Fs
  ( fsCache
  ) where

import Prelude

import Control.Promise (Promise, toAffE)
import Data.ArrayBuffer.Types (Uint8Array)
import Data.Maybe (Maybe)
import Data.Nullable (Nullable, toMaybe)
import Effect (Effect)
import Snarky.Example.Srs.Cache (SrsCache, SrsEntry, entryKey)

-- Read returns `null` on a missing file (cache miss); any other error rejects.
foreign import _get :: String -> String -> Effect (Promise (Nullable Uint8Array))
foreign import _put :: String -> String -> Uint8Array -> Effect (Promise Unit)

-- | Persist SRS entries as files under `dir` (created on first write). `entryKey`
-- | is already filename-safe (no path separators).
fsCache :: String -> SrsCache
fsCache dir =
  { get: \e -> toMaybe <$> toAffE (_get dir (entryKey e))
  , put: \e bytes -> toAffE (_put dir (entryKey e) bytes)
  }
