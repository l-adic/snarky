import { createRequire } from 'module';
const require = createRequire(import.meta.url);
const napi = require('snarky-crypto');

// FIELD-REP COMPAT SHIM — Vesta Poseidon's field is Vesta.BaseField = Fq
// (= PallasScalarField in snarky-crypto naming).
const toFq = (b) => napi.pallasScalarfieldFromBigint(b);
const fromFq = (e) => napi.pallasScalarfieldToBigint(e);

// ============================================================================
// VESTA POSEIDON FFI
// ============================================================================

export function sbox(x) {
    return fromFq(napi.vestaPoseidonSbox(toFq(x)));
}

export function applyMds(state) {
    return napi.vestaPoseidonApplyMds(state.map(toFq)).map(fromFq);
}

export function fullRound(state) {
    return function(roundIndex) {
        return napi.vestaPoseidonFullRound(state.map(toFq), roundIndex).map(fromFq);
    };
}

export function getRoundConstants(roundIndex) {
    return napi.vestaPoseidonGetRoundConstants(roundIndex).map(fromFq);
}

export function getNumRounds() {
    return napi.vestaPoseidonGetNumRounds();
}

export function getMdsMatrix() {
    return napi.vestaPoseidonGetMdsMatrix().map((row) => row.map(fromFq));
}

export function hash(inputs) {
    return fromFq(napi.vestaPoseidonHash(inputs.map(toFq)));
}
