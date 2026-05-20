// Sideload-fixture serde JS bindings.
//
// Pickles' OCaml-side dump format is `serde_json` of the kimchi structs
// `ProverProof<G, OpeningProof<G>>` and `VerifierIndex<G, OpeningProof<G>>`.
// The matching codecs live in `kimchi-napi` as
// `caml_pasta_f{p,q}_plonk_{proof,verifier_index}_{to,from}_json`. Same
// upstream struct, same serde derive on both ends, so cross-stack-
// compatible by construction.
//
// `vestaHydrateVerifierIndex` is preserved as a vestigial identity to
// keep the PS-side API surface stable (FFI.purs signature unchanged).
// Hydration — recomputing `linearization`, `powers_of_alpha`, `w`, and
// `permutation_vanishing_polynomial_m` from the feature flags — now
// happens automatically inside `From<NapiPlonkVerifierIndex> for
// VerifierIndex<G>` (`kimchi-napi/src/plonk_verifier_index.rs:340`),
// triggered whenever a downstream caller (verify, prove) consumes a
// freshly-deserialized VK.

import { createRequire } from 'module';
const require = createRequire(import.meta.url);
const k = require('kimchi-napi');

// Wrap-side (Pallas-curve commitments) VK serde — `vesta*` per the
// PS-side naming convention.
export function vestaVerifierIndexToSerdeJson(vi) {
  return k.caml_pasta_fq_plonk_verifier_index_to_json(vi);
}

export function vestaVerifierIndexFromSerdeJson(json) {
  return function (crs) {
    // PS CRS is `{ srs, size }`; napi takes the raw SRS handle.
    return k.caml_pasta_fq_plonk_verifier_index_from_json(json, crs.srs);
  };
}

// Hydration is automatic in the napi conversion; this is a no-op kept
// for ABI stability with `Pickles.Sideload.FFI.purs`. Args ignored.
export function vestaHydrateVerifierIndex(vk) {
  return function (_flags) {
    return function (_generic) {
      return vk;
    };
  };
}

// Wrap-side (Pallas-curve commitments) proof serde.
export function vestaProofFromSerdeJson(json) {
  return k.caml_pasta_fq_plonk_proof_from_json(json);
}

export function vestaProofToSerdeJson(proof) {
  return k.caml_pasta_fq_plonk_proof_to_json(proof);
}

// Step-side (Vesta-curve commitments) proof serde.
export function pallasProofToSerdeJson(proof) {
  return k.caml_pasta_fp_plonk_proof_to_json(proof);
}

export function pallasProofFromSerdeJson(json) {
  return k.caml_pasta_fp_plonk_proof_from_json(json);
}
