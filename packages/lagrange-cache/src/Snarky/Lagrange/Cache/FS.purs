-- | A filesystem-backed `LagrangeCache` for the Node runtime (tests, the
-- | benchmark, the terminal app): one file per basis under a directory, so the
-- | Lagrange bases survive across process runs. NODE ONLY — its FFI imports
-- | `node:fs`; the browser uses `Snarky.Lagrange.Cache.Idb`.
-- |
-- | Synchronous (`Node.FS.Sync`), to feed the synchronous compile-time warm
-- | without yielding (a yield would let a spec timeout preempt the cold FFT).
module Snarky.Lagrange.Cache.FS
  ( fsCache
  , defaultDir
  ) where

import Prelude

import Data.ArrayBuffer.Typed (buffer, whole) as Typed
import Data.ArrayBuffer.Types (Uint8Array)
import Data.Maybe (Maybe(..))
import Effect (Effect)
import Effect.Random (randomInt)
import Node.Buffer (Buffer)
import Node.Buffer as Buffer
import Node.FS.Perms (Perms, all, mkPerms)
import Node.FS.Sync (exists, mkdir', readFile, rename, writeFile)
import Node.OS (tmpdir)
import Node.Path (FilePath, concat)
import Node.Process (lookupEnv)
import Snarky.Lagrange.Cache (BasisKey, LagrangeCache, keyString)

-- | The on-disk cache directory shared by every Node process (and reused across
-- | runs): `SNARK_LAGRANGE_CACHE_DIR`, or `<tmpdir>/snarky-lagrange-cache`.
defaultDir :: Effect FilePath
defaultDir =
  lookupEnv "SNARK_LAGRANGE_CACHE_DIR" >>= case _ of
    Just dir -> pure dir
    Nothing -> tmpdir <#> \tmp -> concat [ tmp, "snarky-lagrange-cache" ]

-- | Persist bases as files under `dir` (created on first write), via an atomic
-- | write-then-rename so a concurrent reader never sees a half-written blob.
fsCache :: FilePath -> LagrangeCache
fsCache dir =
  { get: \k ->
      let
        path = entryPath dir k
      in
        exists path >>= case _ of
          false -> pure Nothing
          true -> Just <$> (readFile path >>= fromBuffer)
  , put: \k bytes -> do
      mkdir' dir { recursive: true, mode: dirPerms }
      buf <- toBuffer bytes
      tmp <- tempPath dir k
      writeFile tmp buf
      rename tmp (entryPath dir k)
  }

entryPath :: FilePath -> BasisKey -> FilePath
entryPath dir k = concat [ dir, keyString k ]

-- | A unique sibling temp path for an atomic write (random suffix: worker
-- | threads share a pid, so a pid/counter would collide between concurrent cold
-- | builds of the same entry; randomness doesn't).
tempPath :: FilePath -> BasisKey -> Effect FilePath
tempPath dir k = do
  n <- randomInt 0 0x7fffffff
  pure (concat [ dir, "." <> keyString k <> "." <> show n <> ".tmp" ])

dirPerms :: Perms
dirPerms = mkPerms all all all

-- | The kimchi bindings speak `Uint8Array`; node-fs speaks `Buffer`. Same
-- | runtime representation, bridged through the typed-array view.
toBuffer :: Uint8Array -> Effect Buffer
toBuffer = Buffer.fromArrayBuffer <<< Typed.buffer

fromBuffer :: Buffer -> Effect Uint8Array
fromBuffer buf = Buffer.toArrayBuffer buf >>= Typed.whole
