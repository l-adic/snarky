-- | An abstract SRS cache manager: build each curve's generators and per-domain
-- | Lagrange bases ONCE, persist the serialized bytes, and on every later run
-- | load + inject them instead of re-running the (memory-bound) FFTs. See
-- | `docs/srs-sharing-plan.md`.
-- |
-- | Two layers, mirroring `Snarky.Example.P2P.Transport`:
-- |
-- |   * `SrsCache` — the ONLY thing a platform implements: get/put bytes keyed
-- |     by an `SrsEntry`. Async, to admit IndexedDB. Backed by the filesystem in
-- |     Node and IndexedDB in the browser (both in `app/`); `nullCache` /
-- |     `memoryCache` here for the default + tests.
-- |   * the `ensure*` manager — the FFT-on-miss orchestration, written once and
-- |     Node-testable. The platform never sees the kimchi bindings.
-- |
-- | The SRS is a property of the proving system (curve + size + domains), not of
-- | the chain or circuit, so the entry IS the key — a param change is
-- | automatically a miss. `*CrsCreate size` is deterministic, so caching the
-- | generators is a perf choice (skip the rebuild), not a correctness one: a
-- | freshly-created generator set is always consistent with cached bases.
module Snarky.Example.Srs.Cache
  ( SrsEntry(..)
  , entryKey
  , SrsCache
  , nullCache
  , memoryCache
  , SrsOps
  , vestaOps
  , pallasOps
  , ensureGenerators
  , ensureBasis
  , ensureSrs
  ) where

import Prelude

import Data.ArrayBuffer.Types (Uint8Array)
import Data.Foldable (for_)
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Effect (Effect)
import Effect.Aff (Aff)
import Effect.Class (liftEffect)
import Effect.Ref as Ref
import Snarky.Backend.Kimchi.Impl.Pallas as P
import Snarky.Backend.Kimchi.Impl.Vesta as V
import Snarky.Backend.Kimchi.Types (CRS)
import Snarky.Curves.Pasta (PallasG, VestaG)

-- | What a single cache entry addresses: a curve's generators (curve + size), or
-- | one domain's Lagrange basis (curve + size + domain log2). The platform
-- | backend renders it to a file path / IndexedDB key via `entryKey`.
data SrsEntry
  = Generators String Int
  | Basis String Int Int

-- | A stable, self-describing key. The leading `v1` is the blob-format version —
-- | bump it only if the serialization format itself changes (curve/size/domain
-- | changes invalidate automatically, being part of the key).
entryKey :: SrsEntry -> String
entryKey = case _ of
  Generators curve size -> "v1-" <> curve <> "-" <> show size <> "-gen"
  Basis curve size log2 -> "v1-" <> curve <> "-" <> show size <> "-d" <> show log2

-- | The platform persistence interface — the only thing Node/the browser supply.
type SrsCache =
  { get :: SrsEntry -> Aff (Maybe Uint8Array)
  , put :: SrsEntry -> Uint8Array -> Aff Unit
  }

-- | A cache that never persists (every lookup misses): the safe default, and
-- | equivalent to the un-cached FFT path.
nullCache :: SrsCache
nullCache =
  { get: \_ -> pure Nothing
  , put: \_ _ -> pure unit
  }

-- | In-memory blob store (a `Ref` of `Map`), for Node tests / runs without a
-- | filesystem.
memoryCache :: Effect SrsCache
memoryCache = do
  ref <- Ref.new (Map.empty :: Map String Uint8Array)
  pure
    { get: \e -> liftEffect (Map.lookup (entryKey e) <$> Ref.read ref)
    , put: \e bytes -> liftEffect (Ref.modify_ (Map.insert (entryKey e) bytes) ref)
    }

-- | The per-curve kimchi operations the manager needs. Bundled as a record so
-- | the manager is generic over the curve while the platform stays oblivious to
-- | both curves and bindings.
type SrsOps g =
  { curve :: String
  , create :: Int -> CRS g
  , addBasis :: CRS g -> Int -> Effect Unit
  , basisToBytes :: CRS g -> Int -> Effect Uint8Array
  , setBasisFromBytes :: CRS g -> Int -> Uint8Array -> Effect Unit
  , genToBytes :: CRS g -> Effect Uint8Array
  , genFromBytes :: Int -> Uint8Array -> Effect (CRS g)
  }

vestaOps :: SrsOps VestaG
vestaOps =
  { curve: "vesta"
  , create: V.vestaCrsCreate
  , addBasis: V.vestaSrsAddLagrangeBasis
  , basisToBytes: V.vestaSrsLagrangeBasisToBytes
  , setBasisFromBytes: V.vestaSrsSetLagrangeBasisFromBytes
  , genToBytes: V.vestaSrsToBytes
  , genFromBytes: V.vestaSrsFromBytes
  }

pallasOps :: SrsOps PallasG
pallasOps =
  { curve: "pallas"
  , create: P.pallasCrsCreate
  , addBasis: P.pallasSrsAddLagrangeBasis
  , basisToBytes: P.pallasSrsLagrangeBasisToBytes
  , setBasisFromBytes: P.pallasSrsSetLagrangeBasisFromBytes
  , genToBytes: P.pallasSrsToBytes
  , genFromBytes: P.pallasSrsFromBytes
  }

-- | Load the SRS generators for `size` from the cache (deserialize), or create
-- | them (deterministic), store, and return.
ensureGenerators :: forall g. SrsCache -> SrsOps g -> Int -> Aff (CRS g)
ensureGenerators cache ops size =
  cache.get (Generators ops.curve size) >>= case _ of
    Just bytes -> liftEffect (ops.genFromBytes size bytes)
    Nothing -> do
      let crs = ops.create size
      bytes <- liftEffect (ops.genToBytes crs)
      cache.put (Generators ops.curve size) bytes
      pure crs

-- | Ensure `crs` has the Lagrange basis for domain `2^log2`: inject it from the
-- | cache, or run the FFT (`addBasis`), serialize, and store. Mutates `crs`.
ensureBasis :: forall g. SrsCache -> SrsOps g -> CRS g -> Int -> Int -> Aff Unit
ensureBasis cache ops crs size log2 =
  cache.get (Basis ops.curve size log2) >>= case _ of
    Just bytes -> liftEffect (ops.setBasisFromBytes crs log2 bytes)
    Nothing -> do
      liftEffect (ops.addBasis crs log2)
      bytes <- liftEffect (ops.basisToBytes crs log2)
      cache.put (Basis ops.curve size log2) bytes

-- | A warmed SRS of `size` with bases for every domain in `domains`, building
-- | (and caching) only what the cache is missing.
ensureSrs :: forall g. SrsCache -> SrsOps g -> Int -> Array Int -> Aff (CRS g)
ensureSrs cache ops size domains = do
  crs <- ensureGenerators cache ops size
  for_ domains (ensureBasis cache ops crs size)
  pure crs
