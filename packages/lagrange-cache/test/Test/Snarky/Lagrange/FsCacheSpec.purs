-- | Filesystem-backend test (`Snarky.Lagrange.Cache.FS`): a cold cache FFTs a
-- | domain once and writes the basis to disk; a FRESH handle over the same
-- | directory — a new process / reload — injects it with NO further FFT. The
-- | persistence win, without a browser.
module Test.Snarky.Lagrange.FsCacheSpec
  ( spec
  ) where

import Prelude

import Effect (Effect)
import Effect.Aff (Aff)
import Effect.Class (liftEffect)
import Effect.Ref as Ref
import Snarky.Backend.Kimchi.Impl.Vesta as V
import Snarky.Lagrange.Cache (ensureBasis, fingerprint, vestaOps)
import Snarky.Lagrange.Cache.FS (fsCache)
import Test.Spec (SpecT, describe, it)
import Test.Spec.Assertions (shouldEqual)

-- | A fresh empty temp directory (node `fs.mkdtempSync`).
foreign import mkTmpDir :: Effect String

spec :: SpecT Aff Unit Aff Unit
spec = describe "Snarky.Lagrange.Cache.FS (filesystem)" do
  it "persists a basis to disk; a fresh handle reloads it with no re-FFT" do
    dir <- liftEffect mkTmpDir
    let
      size = 8192
      domain = 11
      crs = V.vestaCrsCreate size
    fftCount <- liftEffect (Ref.new 0)
    let ops = vestaOps { addBasis = \c d -> Ref.modify_ (_ + 1) fftCount *> vestaOps.addBasis c d }
    srsHash <- liftEffect $ fingerprint ops crs

    -- Cold: one FFT, basis written to disk under the fingerprint key.
    liftEffect $ ensureBasis (fsCache dir) ops crs srsHash domain
    cold <- liftEffect (Ref.read fftCount)

    -- Warm: a fresh handle + a fresh same-URS SRS reloads the basis, no FFT.
    let crs2 = V.vestaCrsCreate size
    liftEffect $ ensureBasis (fsCache dir) ops crs2 srsHash domain
    warm <- liftEffect (Ref.read fftCount)

    cold `shouldEqual` 1
    warm `shouldEqual` 1
