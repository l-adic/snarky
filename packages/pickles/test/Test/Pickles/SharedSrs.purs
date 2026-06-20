-- | Per-suite SRS shared by every pickles test. SRS construction is
-- | structurally expensive — the kimchi-napi `caml_f{p,q}_srs_create` call
-- | is fast, but the *lagrange basis cache* attached to the SRS is
-- | populated lazily on first use and rebuilt from scratch for every fresh
-- | SRS instance. Per-test SRSes therefore burn ~tens of seconds rebuilding
-- | the same lagrange basis over and over.
-- |
-- | Mounted via `beforeAll buildSharedSrs` in `Test.Pickles.Main`; every
-- | spec under that wrap takes a `SharedSrs` instead of `Unit` as the
-- | per-test value.
-- |
-- | The wrap SRS depth (`wrapSrsDepthLog2 = 15`) is the OCaml Tock URS
-- | convention — `Backend.Tock.Rounds.n = N15` in `kimchi_pasta_basic.ml`.
-- | The step SRS uses the default cache-load (= 2^16, OCaml's Tick URS).
-- | Both depth constants are exported so downstream test helpers
-- | (`Test.Pickles.Sideload.Loader`) can reference the same source of
-- | truth instead of redefining them.
module Test.Pickles.SharedSrs
  ( SharedSrs
  , buildSharedSrs
  , wrapSrsDepthLog2
  ) where

import Prelude

import Colog (LoggerT, Message, logInfo)
import Data.Int.Bits as Int
import Effect.Aff (Aff)
import Effect.Class (liftEffect)
import Pickles (StepField)
import Snarky.Backend.Kimchi.Class (createCRS)
import Snarky.Backend.Kimchi.Impl.Pallas as PallasImpl
import Snarky.Backend.Kimchi.Types (CRS)
import Snarky.Curves.Pasta (PallasG, VestaG)
import Snarky.Lagrange.Cache (LagrangeCache)
import Snarky.Lagrange.Cache.FS (defaultDir, fsCache)

-- | Wrap-side SRS depth (log2). Matches OCaml `Backend.Tock.Rounds.n =
-- | N15` (`kimchi_pasta_basic.ml`). Single source of truth for the wrap
-- | SRS dimension — every consumer (here in `buildSharedSrs`, and the
-- | sideload `loadFixture` helper) imports this constant.
wrapSrsDepthLog2 :: Int
wrapSrsDepthLog2 = 15

-- | The shared SRS *generators* plus the on-disk Lagrange-basis cache. The
-- | bases are NOT pre-warmed here — each pickles test threads `lagrangeCache`
-- | into its `compileMulti` config, and compile warms exactly the domains the
-- | program uses (once ever, persisted, then injected). The same `cache`
-- | handle is shared so every suite reuses one on-disk basis set.
type SharedSrs =
  { pallasSrs :: CRS PallasG
  , vestaSrs :: CRS VestaG
  , lagrangeCache :: LagrangeCache
  }

buildSharedSrs :: LoggerT Message Aff SharedSrs
buildSharedSrs = do
  -- The SRS generators are built directly (fast, deterministic, FFT-free, so
  -- this hook never risks the runner's per-hook Aff timeout). The expensive
  -- Lagrange bases are materialized lazily and persisted by compile (the warm in
  -- `runMultiCompileFull`), at exactly the domains each program commits over.
  logInfo "[SharedSrs] building SRS generators (Lagrange bases warmed lazily at compile)…"
  liftEffect do
    vestaSrs <- createCRS @StepField
    let pallasSrs = PallasImpl.pallasCrsCreate (1 `Int.shl` wrapSrsDepthLog2)
    lagrangeCache <- fsCache <$> defaultDir
    pure { pallasSrs, vestaSrs, lagrangeCache }
