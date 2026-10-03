// Vesta-base Poseidon FFI — host-side hash and permutation ops over Fq
// (Vesta.BaseField = Pallas.ScalarField).
//
// The granular ops run the pure-JS `pasta-runtime` Poseidon spec,
// parameterized by `poseidonParamsKimchiFq` (constants extracted from
// `mina_poseidon::pasta::fq_kimchi`). The whole permutation, and `hash`
// over it, run kimchi-napi's `caml_pasta_fq_poseidon_block_cipher`: the
// same function as the 55 `fullRound`s in order, without the per-round
// states.
//
// PS-side type: `PoseidonField Vesta.BaseField`.

import { createRequire } from 'module';
import { Fq, PoseidonFq, bigintsToBytes32LE } from 'pasta-runtime';

const require = createRequire(import.meta.url);
const k = require('kimchi-napi');

// The permutation on a state in place: a flat 32-byte-LE vector in and
// out.
function blockCipher(state) {
  const out = k.caml_pasta_fq_poseidon_block_cipher(bigintsToBytes32LE(state));
  const bytes = out instanceof Uint8Array ? out : new Uint8Array(out);
  for (let i = 0; i < state.length; i++) {
    state[i] = Fq.fromBytesLE(bytes.subarray(32 * i, 32 * i + 32));
  }
}

export function sbox(x) { return PoseidonFq.sbox(x); }
export function applyMds(state) { return PoseidonFq.applyMds(state); }
export function fullRound(state) { return (i) => PoseidonFq.fullRound(state, i); }
export function permutation(state) {
  const next = [...state];
  blockCipher(next);
  return next;
}
export function getRoundConstants(i) { return PoseidonFq.getRoundConstants(i); }
export function getNumRounds() { return PoseidonFq.getNumRounds(); }
export function getMdsMatrix() { return PoseidonFq.getMdsMatrix(); }
export function hash(inputs) { return PoseidonFq.hash(inputs, blockCipher); }
