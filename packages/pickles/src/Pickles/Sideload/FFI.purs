-- | FFI wrappers for kimchi VK + proof serde-JSON.
-- |
-- | VK serde is wrap-only (`Proof Pallas.G Vesta.BaseField`). Proof
-- | serde covers both the WRAP proof (`Proof Pallas.G Vesta.BaseField`,
-- | `vesta*`) and the STEP proof (`Proof Vesta.G Pallas.BaseField`,
-- | `pallas*`) — the disk proof-cache round-trips both, mirroring OCaml
-- | `Backend.Tock/Tick.Proof.{to,of}_yojson`.
-- |
-- | The wire format is exactly `serde_json::{to_string,from_str}` on
-- | kimchi's standard `ProverProof<G>` / `VerifierIndex<G>` Serde derives —
-- | cross-stack-compatible with the OCaml-emitted fixtures by
-- | construction. Public input is `#[serde(skip)]`; callers thread it
-- | separately. VK hydration (linearization / powers_of_alpha / w /
-- | permutation_vanishing_polynomial_m) is automatic in the kimchi-napi
-- | conversion (`plonk_verifier_index.rs:340`'s
-- | `From<NapiPlonkVerifierIndex> for VerifierIndex`), so no explicit
-- | hydrate step is needed.
module Pickles.Sideload.FFI
  ( vestaVerifierIndexToSerdeJson
  , vestaVerifierIndexFromSerdeJson
  , vestaProofFromSerdeJson
  , vestaProofToSerdeJson
  , pallasProofFromSerdeJson
  , pallasProofToSerdeJson
  ) where

import Pickles.Prove.FFI (Proof)
import Snarky.Backend.Kimchi.Types (CRS, VerifierIndex)
import Snarky.Curves.Pallas as Pallas
import Snarky.Curves.Vesta as Vesta

-- | Vesta-protocol VK serde JSON.
foreign import vestaVerifierIndexToSerdeJson :: VerifierIndex Pallas.G Vesta.BaseField -> String

-- | Inverse of `vestaVerifierIndexToSerdeJson`. Reattaches the supplied
-- | SRS (skipped on serialize).
foreign import vestaVerifierIndexFromSerdeJson
  :: String
  -> CRS Pallas.G
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
