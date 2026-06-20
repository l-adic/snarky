-- | A persistent cache for kimchi **Lagrange bases** — the one expensive,
-- | reusable product of an SRS. The SRS *generators* are a cheap, deterministic
-- | hash-to-curve string the caller always builds itself; only the per-domain
-- | Lagrange bases (commitments of the Lagrange polynomials over the supplied
-- | SRS) are worth persisting, because computing them is a memory-bound FFT.
-- |
-- | A basis is committed *against a specific SRS*, so the cache key carries a
-- | **fingerprint of that SRS** (a blake2b digest of its serialized generators),
-- | not just the curve + domain: two different SRSes for the same curve never
-- | collide, and a basis is only ever injected onto the SRS it was built from.
-- | For the deterministic Pasta URS the fingerprint is constant per curve+size,
-- | so cross-run / cross-process sharing still works.
-- |
-- | The cache is synchronous (`Effect` get/put) because it feeds the synchronous
-- | compile-time warm; an async backend (browser IndexedDB) adapts to this seam
-- | via `Snarky.Lagrange.Cache.Hydrated` (load once, serve from memory, persist
-- | fire-and-forget).
module Snarky.Lagrange.Cache
  ( BasisKey
  , keyString
  , LagrangeCache
  , nullCache
  , memoryCache
  , loggingCache
  , CurveOps
  , vestaOps
  , pallasOps
  , fingerprint
  , ensureBasis
  , warmer
  ) where

import Prelude

import Data.ArrayBuffer.Types (Uint8Array)
import Data.Blake2b (blake2bHex)
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Effect (Effect)
import Effect.Ref as Ref
import Snarky.Backend.Kimchi.Impl.Pallas as P
import Snarky.Backend.Kimchi.Impl.Vesta as V
import Snarky.Backend.Kimchi.Types (CRS)
import Snarky.Curves.Pasta (PallasG, VestaG)

-- | What a cached Lagrange basis is addressed by: the curve, a fingerprint of
-- | the SRS it was committed against, and the domain log2.
type BasisKey = { curve :: String, srsHash :: String, log2 :: Int }

-- | A stable, self-describing key. `v1` is the blob-format version — bump only if
-- | the basis serialization itself changes (curve / SRS / domain changes
-- | invalidate automatically, being part of the key).
keyString :: BasisKey -> String
keyString k = "v1-" <> k.curve <> "-" <> k.srsHash <> "-d" <> show k.log2

-- | The platform persistence interface — the only thing a backend supplies.
-- | Synchronous, to feed the synchronous compile warm.
type LagrangeCache =
  { get :: BasisKey -> Effect (Maybe Uint8Array)
  , put :: BasisKey -> Uint8Array -> Effect Unit
  }

-- | A cache that never persists (every lookup misses): the safe default, and
-- | equivalent to the un-cached always-FFT path.
nullCache :: LagrangeCache
nullCache =
  { get: \_ -> pure Nothing
  , put: \_ _ -> pure unit
  }

-- | In-memory blob store (a `Ref` of `Map`), for tests / runs without a
-- | filesystem, and the working set behind the hydrate/flush adapter.
memoryCache :: Effect LagrangeCache
memoryCache = do
  ref <- Ref.new (Map.empty :: Map String Uint8Array)
  pure
    { get: \k -> Map.lookup (keyString k) <$> Ref.read ref
    , put: \k bytes -> Ref.modify_ (Map.insert (keyString k) bytes) ref
    }

-- | Wrap a cache so every lookup logs HIT (inject, no FFT) or MISS (FFT + store)
-- | through `sink` — caller picks the level (e.g. `Log.logDebug logger`).
loggingCache :: (String -> Effect Unit) -> LagrangeCache -> LagrangeCache
loggingCache sink inner = inner
  { get = \k -> do
      r <- inner.get k
      sink $ case r of
        Just _ -> "[lagrange-cache] hit " <> keyString k <> " (inject, no FFT)"
        Nothing -> "[lagrange-cache] miss " <> keyString k <> " (FFT + store)"
      pure r
  }

-- | The per-curve kimchi ops the cache needs: a canonical byte image of the SRS
-- | generators (for the fingerprint) and the Lagrange-basis FFT + serde.
type CurveOps g =
  { curve :: String
  , srsToBytes :: CRS g -> Effect Uint8Array
  , addBasis :: CRS g -> Int -> Effect Unit
  , basisToBytes :: CRS g -> Int -> Effect Uint8Array
  , setBasisFromBytes :: CRS g -> Int -> Uint8Array -> Effect Unit
  }

vestaOps :: CurveOps VestaG
vestaOps =
  { curve: "vesta"
  , srsToBytes: V.vestaSrsToBytes
  , addBasis: V.vestaSrsAddLagrangeBasis
  , basisToBytes: V.vestaSrsLagrangeBasisToBytes
  , setBasisFromBytes: V.vestaSrsSetLagrangeBasisFromBytes
  }

pallasOps :: CurveOps PallasG
pallasOps =
  { curve: "pallas"
  , srsToBytes: P.pallasSrsToBytes
  , addBasis: P.pallasSrsAddLagrangeBasis
  , basisToBytes: P.pallasSrsLagrangeBasisToBytes
  , setBasisFromBytes: P.pallasSrsSetLagrangeBasisFromBytes
  }

-- | Fingerprint an SRS by hashing its serialized generators: a 128-bit blake2b
-- | digest, hex. Synchronous (blakejs, via `Data.Blake2b`) so it runs inside the
-- | compile-time warm, and browser-safe (unlike `crypto.subtle`).
fingerprint :: forall g. CurveOps g -> CRS g -> Effect String
fingerprint ops crs = blake2bHex 16 <$> ops.srsToBytes crs

-- | Ensure `crs` holds the Lagrange basis for domain `2^log2`, keyed by the SRS
-- | fingerprint `srsHash`: inject from the cache (no FFT), or run the FFT
-- | (`addBasis`), serialize, and store. Mutates `crs`.
ensureBasis :: forall g. LagrangeCache -> CurveOps g -> CRS g -> String -> Int -> Effect Unit
ensureBasis cache ops crs srsHash log2 =
  cache.get key >>= case _ of
    Just bytes -> ops.setBasisFromBytes crs log2 bytes
    Nothing -> do
      ops.addBasis crs log2
      bytes <- ops.basisToBytes crs log2
      cache.put key bytes
  where
  key = { curve: ops.curve, srsHash, log2 }

-- | Bundle a cache + curve + SRS into a per-domain warmer, computing the SRS
-- | fingerprint ONCE (not per domain). `warmer cache ops crs >>= \w -> for_ ds w`.
warmer :: forall g. LagrangeCache -> CurveOps g -> CRS g -> Effect (Int -> Effect Unit)
warmer cache ops crs = do
  srsHash <- fingerprint ops crs
  pure (ensureBasis cache ops crs srsHash)
