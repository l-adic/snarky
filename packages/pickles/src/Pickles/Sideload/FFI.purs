-- | Side-loading FFI wrappers for kimchi VK + proof JSON serialization.
-- |
-- | These are the PS-side counterparts to the Rust serde JSON bindings added
-- | in kimchi-stubs (`caml_pasta_{fp,fq}_plonk_{verifier_index,proof}_{to,of}_serde_json`)
-- | and crypto-provider (`{pallas,vesta}_{verifier_index,proof}_{to,from}_serde_json`).
-- |
-- | Naming follows `pallasCreateProof`/`vestaCreateProof`: the `pallas`-prefixed
-- | functions operate on Pallas-protocol (Fp scalar field, Vesta-curve commitments
-- | → `Proof Vesta.G Pallas.BaseField`); the `vesta`-prefixed ones operate on
-- | Vesta-protocol (Fq, Pallas-curve → `Proof Pallas.G Vesta.BaseField`).
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

-- | Caller-supplied feature flags for VK hydration. Mirrors kimchi's
-- | `FeatureFlags` (constraints.rs:46-61). For Pickles wrap proofs all
-- | of these are `false`; use `noOptionalFeatures`.
type VkFeatureFlags =
  { rangeCheck0 :: Boolean
  , rangeCheck1 :: Boolean
  , foreignFieldAdd :: Boolean
  , foreignFieldMul :: Boolean
  , xor :: Boolean
  , rot :: Boolean
  , lookup :: Boolean
  }

-- | The "no optional features" preset used by Pickles wrap circuits.
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

-- | VerifierIndex serde JSON for the Pallas-protocol VK (Vesta-curve commitments).
foreign import pallasVerifierIndexToSerdeJson :: VerifierIndex Vesta.G Pallas.BaseField -> String

-- | Inverse of `pallasVerifierIndexToSerdeJson`. Reattaches the supplied
-- | SRS (skipped on serialize via `#[serde(skip)]`). The kimchi VK's
-- | `linearization` and `powers_of_alpha` fields are also `#[serde(skip)]`
-- | and come back empty; the result is therefore *dehydrated*. Pipe
-- | through `pallasHydrateVerifierIndex` before passing to verify.
foreign import pallasVerifierIndexFromSerdeJson
  :: String
  -> CRS Vesta.G
  -> Dehydrated (VerifierIndex Vesta.G Pallas.BaseField)

-- | Hydrate a deserialized Pallas-protocol VK. Recomputes
-- | `linearization` + `powers_of_alpha` from the supplied feature flags
-- | (mirrors `prover_index.rs:132` and kimchi's serde test
-- | `tests/serde.rs:91-92`). `generic = true` includes the Generic gate
-- | constraints — Pickles wrap proofs always have this.
foreign import pallasHydrateVerifierIndex
  :: Dehydrated (VerifierIndex Vesta.G Pallas.BaseField)
  -> VkFeatureFlags
  -> Boolean
  -> VerifierIndex Vesta.G Pallas.BaseField

-- | VerifierIndex serde JSON for the Vesta-protocol VK (Pallas-curve commitments).
foreign import vestaVerifierIndexToSerdeJson :: VerifierIndex Pallas.G Vesta.BaseField -> String

-- | Inverse of `vestaVerifierIndexToSerdeJson`. Result is dehydrated;
-- | see `pallasVerifierIndexFromSerdeJson` for the lifecycle.
foreign import vestaVerifierIndexFromSerdeJson
  :: String
  -> CRS Pallas.G
  -> Dehydrated (VerifierIndex Pallas.G Vesta.BaseField)

-- | Hydrate a deserialized Vesta-protocol VK. See
-- | `pallasHydrateVerifierIndex` for argument semantics.
foreign import vestaHydrateVerifierIndex
  :: Dehydrated (VerifierIndex Pallas.G Vesta.BaseField)
  -> VkFeatureFlags
  -> Boolean
  -> VerifierIndex Pallas.G Vesta.BaseField

-- | Kimchi `ProverProof` serde JSON for the Pallas-protocol proof (Vesta-curve commitments).
-- | Public input is NOT included in the JSON; callers serialize it separately via
-- | the field type's own JSON encoding.
foreign import pallasProofToSerdeJson :: Proof Vesta.G Pallas.BaseField -> String

-- | Inverse of `pallasProofToSerdeJson`. Public input must be supplied separately.
foreign import pallasProofFromSerdeJson :: String -> Proof Vesta.G Pallas.BaseField

-- | Kimchi `ProverProof` serde JSON for the Vesta-protocol proof (Pallas-curve commitments).
foreign import vestaProofToSerdeJson :: Proof Pallas.G Vesta.BaseField -> String

-- | Inverse of `vestaProofToSerdeJson`.
foreign import vestaProofFromSerdeJson :: String -> Proof Pallas.G Vesta.BaseField
