-- | Core manager test (`Snarky.Lagrange.Cache`) over the in-memory cache: a cold
-- | cache FFTs a domain once and stores it under the SRS fingerprint; a second
-- | SRS *instance* (same deterministic URS → same fingerprint) injects the stored
-- | basis with NO further FFT. A small SRS/domain keeps the FFT quick.
module Test.Snarky.Lagrange.CacheSpec
  ( spec
  ) where

import Prelude

import Data.Maybe (isJust)
import Effect.Aff (Aff)
import Effect.Class (liftEffect)
import Effect.Ref as Ref
import Snarky.Backend.Kimchi.Impl.Vesta as V
import Snarky.Lagrange.Cache (ensureBasis, fingerprint, memoryCache, vestaOps)
import Test.Spec (SpecT, describe, it)
import Test.Spec.Assertions (shouldEqual)

spec :: SpecT Aff Unit Aff Unit
spec = describe "Snarky.Lagrange.Cache (memoryCache + SRS fingerprint)" do
  it "FFTs a domain once on a cold cache, then injects it onto a fresh same-URS SRS with no re-FFT" do
    let
      size = 8192
      domain = 11
      crs = V.vestaCrsCreate size
    fftCount <- liftEffect (Ref.new 0)
    cache <- liftEffect memoryCache
    -- Count the FFT (`addBasis`) by wrapping the real ops.
    let ops = vestaOps { addBasis = \c d -> Ref.modify_ (_ + 1) fftCount *> vestaOps.addBasis c d }
    srsHash <- liftEffect $ fingerprint ops crs

    -- Cold: one FFT; the basis lands under (vesta, fingerprint, domain).
    liftEffect $ ensureBasis cache ops crs srsHash domain
    cold <- liftEffect (Ref.read fftCount)
    stored <- liftEffect $ cache.get { curve: "vesta", srsHash, log2: domain }

    -- A FRESH SRS instance of the same size is the deterministic Pasta URS, so it
    -- has the SAME fingerprint → the cached basis is injected, no FFT.
    let crs2 = V.vestaCrsCreate size
    hash2 <- liftEffect $ fingerprint ops crs2
    liftEffect $ ensureBasis cache ops crs2 hash2 domain
    warm <- liftEffect (Ref.read fftCount)

    cold `shouldEqual` 1
    warm `shouldEqual` 1
    isJust stored `shouldEqual` true
    (hash2 == srsHash) `shouldEqual` true
