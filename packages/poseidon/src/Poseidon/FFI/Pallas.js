// Pallas-base Poseidon FFI — host-side hash and permutation ops over Fp
// (Pallas.BaseField = Vesta.ScalarField).
//
// The granular ops (`sbox`, `applyMds`, `fullRound`, the constants) run
// the pure-JS `pasta-runtime` Poseidon spec, parameterized by
// `poseidonParamsKimchiFp` — the constants `mina_poseidon::pasta::
// fp_kimchi` emits in Rust. A circuit's witness needs them: it holds
// every round's state.
//
// The whole permutation, and `hash` over it, run kimchi-napi's
// `caml_pasta_fp_poseidon_block_cipher`: the same function as the 55
// `fullRound`s in order, without the per-round states.
//
// PS-side type: `PoseidonField Pallas.BaseField` (class instance in
// `Poseidon.Class`). Bigints in, bigints out.

import { createRequire } from 'module';
import { Fp, Poseidon, bigintsToBytes32LE } from 'pasta-runtime';

const require = createRequire(import.meta.url);
const k = require('kimchi-napi');

// The permutation on a state in place: a flat 32-byte-LE vector in and
// out.
function blockCipher(state) {
  const out = k.caml_pasta_fp_poseidon_block_cipher(bigintsToBytes32LE(state));
  const bytes = out instanceof Uint8Array ? out : new Uint8Array(out);
  for (let i = 0; i < state.length; i++) {
    state[i] = Fp.fromBytesLE(bytes.subarray(32 * i, 32 * i + 32));
  }
}

export function sbox(x) { return Poseidon.sbox(x); }
export function applyMds(state) { return Poseidon.applyMds(state); }
export function fullRound(state) { return (i) => Poseidon.fullRound(state, i); }
export function permutation(state) {
  const next = [...state];
  blockCipher(next);
  return next;
}
export function getRoundConstants(i) { return Poseidon.getRoundConstants(i); }
export function getNumRounds() { return Poseidon.getNumRounds(); }
export function getMdsMatrix() { return Poseidon.getMdsMatrix(); }
export function hash(inputs) { return Poseidon.hash(inputs, blockCipher); }
