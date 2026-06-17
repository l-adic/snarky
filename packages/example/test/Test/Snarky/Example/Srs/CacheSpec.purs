-- | Phase-2 test for the SRS cache manager (`Snarky.Example.Srs.Cache`), run in
-- | Node over the in-memory `memoryCache` with no filesystem or browser: a cold
-- | cache FFTs each domain once and stores the generators + bases; a warm cache
-- | serves everything and runs NO further FFT. We count `addBasis` (the FFT) by
-- | wrapping the curve ops. Small SRS/domain for speed — the manager is
-- | size/domain-agnostic.
module Test.Snarky.Example.Srs.CacheSpec
  ( spec
  ) where

import Prelude

import Data.Maybe (isJust)
import Effect.Aff (Aff)
import Effect.Class (liftEffect)
import Effect.Ref as Ref
import Snarky.Example.Srs.Cache (SrsEntry(..), ensureSrs, memoryCache, vestaOps)
import Test.Spec (SpecT, describe, it)
import Test.Spec.Assertions (shouldEqual)

spec :: SpecT Aff Unit Aff Unit
spec = describe "Snarky.Example.Srs.Cache (memoryCache)" do
  it "FFTs each domain once on a cold cache, then serves generators + bases without re-FFTing" do
    let
      size = 8192
      domain = 11
    fftCount <- liftEffect (Ref.new 0)
    cache <- liftEffect memoryCache
    -- Count the FFT (`addBasis`) by wrapping the real ops.
    let ops = vestaOps { addBasis = \crs d -> Ref.modify_ (_ + 1) fftCount *> vestaOps.addBasis crs d }

    -- Cold build: one FFT for the domain; generators + basis land in the cache.
    _ <- ensureSrs cache ops size [ domain ]
    coldFfts <- liftEffect (Ref.read fftCount)
    genCached <- cache.get (Generators "vesta" size)
    basisCached <- cache.get (Basis "vesta" size domain)

    -- Warm build: everything loads from the cache, no further FFT.
    _ <- ensureSrs cache ops size [ domain ]
    warmFfts <- liftEffect (Ref.read fftCount)

    coldFfts `shouldEqual` 1
    warmFfts `shouldEqual` 1
    isJust genCached `shouldEqual` true
    isJust basisCached `shouldEqual` true
