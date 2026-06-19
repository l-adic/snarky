-- | Phase-1 de-risk for the SRS cache manager (see `docs/srs-sharing-plan.md`):
-- | prove that a Lagrange basis survives the out-of-band serde the manager will
-- | rely on. `SRS::Serialize` `#[serde(skip)]`s the bases, so they must be moved
-- | through the dedicated `*_srs_lagrange_basis_to_bytes` / `*_set_lagrange_basis_from_bytes`
-- | bindings instead. We assert, for both curves:
-- |
-- |   * serialize → inject into a FRESH SRS → re-serialize is byte-identical
-- |     (the inject reproduces the basis exactly), and
-- |   * that injected basis equals one built by an INDEPENDENT FFT
-- |     (`add_lagrange_basis`) — i.e. injecting is indistinguishable from
-- |     computing.
-- |
-- | The proving path picks the injected basis up through the very same
-- | `get_or_generate(size, …)` cache the existing `add_lagrange_basis` /
-- | structured `set_lagrange_basis` already drive, so byte-identity is the
-- | load-bearing assertion. Small domains are used for speed; the serde is
-- | domain-agnostic, so the app's real domains (Vesta 13/15, Pallas 14) take
-- | the identical code path.
module Test.Snarky.Backend.Kimchi.SrsCache
  ( spec
  ) where

import Prelude

import Data.ArrayBuffer.Types (Uint8Array)
import Data.Foldable (for_)
import Effect (Effect)
import Effect.Aff (Aff)
import Effect.Class (liftEffect)
import Snarky.Backend.Kimchi.Impl.Pallas as P
import Snarky.Backend.Kimchi.Impl.Vesta as V
import Snarky.Backend.Kimchi.Types (CRS)
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (shouldEqual)

-- | Byte-wise equality of two serialized blobs (length + contents).
foreign import bytesEq :: Uint8Array -> Uint8Array -> Boolean

-- | Test SRS size — a power of two comfortably above every test domain. Far
-- | below the app's 65536/32768 so the FFTs stay quick.
depth :: Int
depth = 8192

-- | For one domain: build the basis by FFT and serialize it; inject that blob
-- | into a fresh SRS and re-serialize; build it a third time by an independent
-- | FFT. Assert the injected basis is byte-identical to both FFT results.
checkCurve
  :: forall g
   . (Int -> CRS g)
  -> (CRS g -> Int -> Effect Unit)
  -> (CRS g -> Int -> Effect Uint8Array)
  -> (CRS g -> Int -> Uint8Array -> Effect Unit)
  -> Int
  -> Aff Unit
checkCurve create addBasis toBytes setFromBytes log2 = do
  bytesFft <- liftEffect do
    let crs = create depth
    addBasis crs log2
    toBytes crs log2
  bytesInjected <- liftEffect do
    let crs = create depth
    setFromBytes crs log2 bytesFft
    toBytes crs log2
  bytesFftAgain <- liftEffect do
    let crs = create depth
    addBasis crs log2
    toBytes crs log2
  bytesEq bytesInjected bytesFft `shouldEqual` true
  bytesEq bytesFftAgain bytesFft `shouldEqual` true

spec :: Spec Unit
spec = describe "Snarky.Backend.Kimchi SRS Lagrange-basis serde (out-of-band cache)" do
  it "Vesta: serialize → inject round-trips byte-identical and matches an independent FFT" do
    for_ [ 11, 12 ] $
      checkCurve V.vestaCrsCreate V.vestaSrsAddLagrangeBasis
        V.vestaSrsLagrangeBasisToBytes
        V.vestaSrsSetLagrangeBasisFromBytes
  it "Pallas: serialize → inject round-trips byte-identical and matches an independent FFT" do
    for_ [ 11, 12 ] $
      checkCurve P.pallasCrsCreate P.pallasSrsAddLagrangeBasis
        P.pallasSrsLagrangeBasisToBytes
        P.pallasSrsSetLagrangeBasisFromBytes
