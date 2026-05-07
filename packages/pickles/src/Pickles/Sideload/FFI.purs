-- | Side-loading FFI wrappers for kimchi VK + proof JSON serialization.
-- |
-- | Naming follows `pallasCreateProof`/`vestaCreateProof`:
-- | `pallas`-prefixed functions operate on the Pallas-protocol (Fp
-- | scalar field, Vesta-curve commitments → `Proof Vesta.G
-- | Pallas.BaseField`); `vesta`-prefixed ones on the Vesta-protocol
-- | (Fq, Pallas-curve → `Proof Pallas.G Vesta.BaseField`).
module Pickles.Sideload.FFI
  ( pallasVerifierIndexToSerdeJson
  , pallasVerifierIndexFromSerdeJson
  , pallasHydrateVerifierIndex
  , vestaVerifierIndexToSerdeJson
  , vestaVerifierIndexFromSerdeJson
  , vestaHydrateVerifierIndex
  , VkFeatureFlags
  , noOptionalFeatures
  , pallasProofToSerdeJson
  , pallasProofFromSerdeJson
  , vestaProofToSerdeJson
  , vestaProofFromSerdeJson
  ) where

import Pickles.ProofFFI (Dehydrated, Proof)
import Snarky.Backend.Kimchi.Types (CRS, VerifierIndex)
import Snarky.Curves.Pallas as Pallas
import Snarky.Curves.Vesta as Vesta

-- | Feature flags for VK hydration; mirrors kimchi's `FeatureFlags`.
-- | Pickles wrap proofs use `noOptionalFeatures`.
type VkFeatureFlags =
  { rangeCheck0 :: Boolean
  , rangeCheck1 :: Boolean
  , foreignFieldAdd :: Boolean
  , foreignFieldMul :: Boolean
  , xor :: Boolean
  , rot :: Boolean
  , lookup :: Boolean
  }

-- | All-`false` preset — what Pickles wrap circuits use.
noOptionalFeatures :: VkFeatureFlags
noOptionalFeatures =
  { rangeCheck0: false
  , rangeCheck1: false
  , foreignFieldAdd: false
  , foreignFieldMul: false
  , xor: false
  , rot: false
  , lookup: false
  }

-- | Pallas-protocol VK serde JSON.
foreign import pallasVerifierIndexToSerdeJson :: VerifierIndex Vesta.G Pallas.BaseField -> String

-- | Inverse of `pallasVerifierIndexToSerdeJson`. Reattaches the
-- | supplied SRS (skipped on serialize). The kimchi VK's
-- | `linearization` and `powers_of_alpha` fields also serde-skip and
-- | come back empty, so the result is *dehydrated* — pipe through
-- | `pallasHydrateVerifierIndex` before verify.
foreign import pallasVerifierIndexFromSerdeJson
  :: String
  -> CRS Vesta.G
  -> Dehydrated (VerifierIndex Vesta.G Pallas.BaseField)

-- | Hydrate a dehydrated Pallas-protocol VK by recomputing
-- | `linearization` + `powers_of_alpha` from the feature flags. The
-- | trailing `Boolean` is `generic` (include Generic gate constraints);
-- | always `true` for Pickles wrap proofs.
foreign import pallasHydrateVerifierIndex
  :: Dehydrated (VerifierIndex Vesta.G Pallas.BaseField)
  -> VkFeatureFlags
  -> Boolean
  -> VerifierIndex Vesta.G Pallas.BaseField

-- | Vesta-protocol VK serde JSON.
foreign import vestaVerifierIndexToSerdeJson :: VerifierIndex Pallas.G Vesta.BaseField -> String

-- | Inverse of `vestaVerifierIndexToSerdeJson`. Dehydrated result;
-- | see `pallasVerifierIndexFromSerdeJson`.
foreign import vestaVerifierIndexFromSerdeJson
  :: String
  -> CRS Pallas.G
  -> Dehydrated (VerifierIndex Pallas.G Vesta.BaseField)

-- | Hydrate a dehydrated Vesta-protocol VK; see
-- | `pallasHydrateVerifierIndex` for argument semantics.
foreign import vestaHydrateVerifierIndex
  :: Dehydrated (VerifierIndex Pallas.G Vesta.BaseField)
  -> VkFeatureFlags
  -> Boolean
  -> VerifierIndex Pallas.G Vesta.BaseField

-- | Pallas-protocol kimchi `ProverProof` serde JSON. Public input is
-- | NOT included; callers serialize it separately.
foreign import pallasProofToSerdeJson :: Proof Vesta.G Pallas.BaseField -> String

-- | Inverse of `pallasProofToSerdeJson`. Public input must be supplied
-- | separately.
foreign import pallasProofFromSerdeJson :: String -> Proof Vesta.G Pallas.BaseField

-- | Vesta-protocol kimchi `ProverProof` serde JSON.
foreign import vestaProofToSerdeJson :: Proof Pallas.G Vesta.BaseField -> String

-- | Inverse of `vestaProofToSerdeJson`.
foreign import vestaProofFromSerdeJson :: String -> Proof Pallas.G Vesta.BaseField
