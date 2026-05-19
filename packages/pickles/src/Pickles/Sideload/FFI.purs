-- | FFI wrappers for kimchi VK + proof serde-JSON.
-- |
-- | VK serde is wrap-only (`Proof Pallas.G Vesta.BaseField`). Proof
-- | serde covers both the WRAP proof (`Proof Pallas.G Vesta.BaseField`,
-- | `vesta*`) and the STEP proof (`Proof Vesta.G Pallas.BaseField`,
-- | `pallas*`) — the disk proof-cache round-trips both, mirroring OCaml
-- | `Backend.Tock/Tick.Proof.{to,of}_yojson`.
module Pickles.Sideload.FFI
  ( VkFeatureFlags
  , vestaVerifierIndexToSerdeJson
  , vestaVerifierIndexFromSerdeJson
  , vestaHydrateVerifierIndex
  , noOptionalFeatures
  , vestaProofFromSerdeJson
  , vestaProofToSerdeJson
  , pallasProofFromSerdeJson
  , pallasProofToSerdeJson
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

-- | Vesta-protocol VK serde JSON.
foreign import vestaVerifierIndexToSerdeJson :: VerifierIndex Pallas.G Vesta.BaseField -> String

-- | Inverse of `vestaVerifierIndexToSerdeJson`. Reattaches the supplied
-- | SRS (skipped on serialize). The kimchi VK's `linearization` and
-- | `powers_of_alpha` fields also serde-skip and come back empty, so
-- | the result is *dehydrated* — pipe through `vestaHydrateVerifierIndex`
-- | before verify.
foreign import vestaVerifierIndexFromSerdeJson
  :: String
  -> CRS Pallas.G
  -> Dehydrated (VerifierIndex Pallas.G Vesta.BaseField)

-- | Hydrate a dehydrated Vesta-protocol VK by recomputing
-- | `linearization` + `powers_of_alpha` from the feature flags. The
-- | trailing `Boolean` is `generic` (include Generic gate constraints);
-- | always `true` for Pickles wrap proofs.
foreign import vestaHydrateVerifierIndex
  :: Dehydrated (VerifierIndex Pallas.G Vesta.BaseField)
  -> VkFeatureFlags
  -> Boolean
  -> VerifierIndex Pallas.G Vesta.BaseField

-- | Vesta-protocol kimchi `ProverProof` serde JSON. Public input is
-- | NOT included; callers serialize it separately.
foreign import vestaProofFromSerdeJson :: String -> Proof Pallas.G Vesta.BaseField

-- | Wrap-proof serialize — inverse of `vestaProofFromSerdeJson`
-- | (= OCaml `Backend.Tock.Proof.to_yojson`).
foreign import vestaProofToSerdeJson :: Proof Pallas.G Vesta.BaseField -> String

-- | Step-proof (Vesta-curve commitments) serde JSON, both directions
-- | (= OCaml `Backend.Tick.Proof.{to,of}_yojson`).
foreign import pallasProofToSerdeJson :: Proof Vesta.G Pallas.BaseField -> String
foreign import pallasProofFromSerdeJson :: String -> Proof Vesta.G Pallas.BaseField
