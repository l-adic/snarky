-- | Phase-3 test for the filesystem SRS cache backend (`Snarky.Example.Srs.Cache.Fs`),
-- | run in Node: a cold cache FFTs each domain once and writes the generators +
-- | bases to disk; a FRESH cache handle over the same directory — standing in for
-- | a new process / page reload — reloads them and runs NO further FFT. This is
-- | the persistence win, validated without a browser.
module Test.Snarky.Example.Srs.FsCacheSpec
  ( spec
  ) where

import Prelude

import Data.Maybe (isJust)
import Effect (Effect)
import Effect.Aff (Aff)
import Effect.Class (liftEffect)
import Effect.Ref as Ref
import Snarky.Example.Srs.Cache (SrsEntry(..), ensureSrs, vestaOps)
import Snarky.Example.Srs.Cache.Fs (fsCache)
import Test.Spec (SpecT, describe, it)
import Test.Spec.Assertions (shouldEqual)

-- | A fresh empty temp directory (node `fs.mkdtempSync`).
foreign import mkTmpDir :: Effect String

spec :: SpecT Aff Unit Aff Unit
spec = describe "Snarky.Example.Srs.Cache.Fs (filesystem)" do
  it "persists generators + bases to disk; a fresh handle reloads them with no re-FFT" do
    dir <- liftEffect mkTmpDir
    fftCount <- liftEffect (Ref.new 0)
    let
      size = 8192
      domain = 11
      countingOps = vestaOps { addBasis = \crs d -> Ref.modify_ (_ + 1) fftCount *> vestaOps.addBasis crs d }

    -- Cold: one FFT, generators + basis written to disk.
    _ <- ensureSrs (fsCache dir) countingOps size [ domain ]
    coldFfts <- liftEffect (Ref.read fftCount)
    genOnDisk <- (fsCache dir).get (Generators "vesta" size)
    basisOnDisk <- (fsCache dir).get (Basis "vesta" size domain)

    -- Warm: a FRESH handle to the same dir (a new "process") reloads, no FFT.
    _ <- ensureSrs (fsCache dir) countingOps size [ domain ]
    warmFfts <- liftEffect (Ref.read fftCount)

    coldFfts `shouldEqual` 1
    warmFfts `shouldEqual` 1
    isJust genOnDisk `shouldEqual` true
    isJust basisOnDisk `shouldEqual` true
