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

import Data.Array as Array
import Data.Foldable (for_)
import Data.Int.Bits as Int
import Effect.Aff (Aff)
import Effect.Class (liftEffect)
import Pickles (StepField)
import Snarky.Backend.Kimchi.Class (addLagrangeBasis, createCRS)
import Snarky.Backend.Kimchi.Impl.Pallas as PallasImpl
import Snarky.Backend.Kimchi.Types (CRS)
import Snarky.Curves.Pasta (PallasG, VestaG)

-- | Wrap-side SRS depth (log2). Matches OCaml `Backend.Tock.Rounds.n =
-- | N15` (`kimchi_pasta_basic.ml`). Single source of truth for the wrap
-- | SRS dimension — every consumer (here in `buildSharedSrs`, and the
-- | sideload `loadFixture` helper) imports this constant.
wrapSrsDepthLog2 :: Int
wrapSrsDepthLog2 = 15

type SharedSrs =
  { pallasSrs :: CRS PallasG
  , vestaSrs :: CRS VestaG
  }

buildSharedSrs :: Aff SharedSrs
buildSharedSrs = liftEffect do
  let pallasSrs = PallasImpl.pallasCrsCreate (1 `Int.shl` wrapSrsDepthLog2)
  vestaSrs <- createCRS @StepField
  -- Pre-warm the lagrange-basis cache (log2 domain sizes) for every
  -- domain the suite's circuits touch, so the first spec to hit each
  -- domain doesn't pay the basis computation — it's front-loaded here,
  -- once, into the shared SRS every spec reuses. Step (Vesta/Fp) domains
  -- run up to 2^16 (Tick URS); wrap (Pallas/Fq) up to 2^15 (Tock URS,
  -- = `wrapSrsDepthLog2`). Warming a domain no spec uses is harmless.
  for_ (Array.range 9 16) (addLagrangeBasis vestaSrs)
  for_ (Array.range 12 wrapSrsDepthLog2) (addLagrangeBasis pallasSrs)
  pure { pallasSrs, vestaSrs }
