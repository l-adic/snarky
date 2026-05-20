// Vesta-base Poseidon FFI — host-side hash + granular permutation ops
// over Fq (Vesta.BaseField = Pallas.ScalarField). Routes through the
// pure-JS `pasta-runtime` Poseidon spec parameterized by
// `poseidonParamsKimchiFq`. Constants are extracted from
// `mina_poseidon::pasta::fq_kimchi`; permutation parity vs
// `caml_pasta_fq_poseidon_block_cipher` byte-for-byte verified.
//
// PS-side type: `PoseidonField Vesta.BaseField`.

import { PoseidonFq } from 'pasta-runtime';

export function sbox(x) { return PoseidonFq.sbox(x); }
export function applyMds(state) { return PoseidonFq.applyMds(state); }
export function fullRound(state) { return (i) => PoseidonFq.fullRound(state, i); }
export function getRoundConstants(i) { return PoseidonFq.getRoundConstants(i); }
export function getNumRounds() { return PoseidonFq.getNumRounds(); }
export function getMdsMatrix() { return PoseidonFq.getMdsMatrix(); }
export function hash(inputs) { return PoseidonFq.hash(inputs); }
