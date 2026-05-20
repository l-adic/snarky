// Pallas-base Poseidon FFI — host-side hash + granular permutation ops
// over Fp (Pallas.BaseField = Vesta.ScalarField). Routes through the
// pure-JS `pasta-runtime` Poseidon spec (which itself is parameterized by
// `poseidonParamsKimchiFp` — the same constants `mina_poseidon::pasta::
// fp_kimchi` emits in Rust, so parity vs `caml_pasta_fp_poseidon_block_cipher`
// is byte-for-byte; see `packages/curves/test/poseidon-parity-harness.mjs`).
//
// PS-side type: `PoseidonField Pallas.BaseField` (class instance in
// `Poseidon.Class`). Bigints in, bigints out.

import { Poseidon } from 'pasta-runtime';

export function sbox(x) { return Poseidon.sbox(x); }
export function applyMds(state) { return Poseidon.applyMds(state); }
export function fullRound(state) { return (i) => Poseidon.fullRound(state, i); }
export function getRoundConstants(i) { return Poseidon.getRoundConstants(i); }
export function getNumRounds() { return Poseidon.getNumRounds(); }
export function getMdsMatrix() { return Poseidon.getMdsMatrix(); }
export function hash(inputs) { return Poseidon.hash(inputs); }
