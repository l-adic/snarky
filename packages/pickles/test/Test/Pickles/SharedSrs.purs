-- | The SRS every pickles test shares, mounted by
-- | `beforeAll buildSharedSrs` in `Test.Pickles.Main` so that each spec
-- | takes a `SharedSrs` as its per-test value.
-- |
-- | Sharing matters because of the Lagrange basis cache attached to an
-- | SRS: creating the generators is fast, but the bases are built
-- | lazily and from scratch for each fresh SRS, which costs tens of
-- | seconds per test.
-- |
-- | The step SRS takes the default depth of 2^16.
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

-- | Wrap-side SRS depth, as a log2. Fixed at 15 by the wrap IPA's
-- | round count.
wrapSrsDepthLog2 :: Int
wrapSrsDepthLog2 = 15

-- | The shared SRS generators plus the on-disk Lagrange-basis cache.
-- | The bases are not pre-warmed: each test threads `lagrangeCache`
-- | into its `compileMulti` config and compile warms exactly the
-- | domains that program commits over, once, persisted.
type SharedSrs =
  { pallasSrs :: CRS PallasG
  , vestaSrs :: CRS VestaG
  , lagrangeCache :: LagrangeCache
  }

buildSharedSrs :: LoggerT Message Aff SharedSrs
buildSharedSrs = do
  -- Building only the generators keeps this hook FFT-free, and so
  -- clear of the runner's per-hook timeout; `runMultiCompileFull`
  -- warms and persists the bases later.
  logInfo "[SharedSrs] building SRS generators (Lagrange bases warmed lazily at compile)…"
  liftEffect do
    vestaSrs <- createCRS @StepField
    let pallasSrs = PallasImpl.pallasCrsCreate (1 `Int.shl` wrapSrsDepthLog2)
    lagrangeCache <- fsCache <$> defaultDir
    pure { pallasSrs, vestaSrs, lagrangeCache }
