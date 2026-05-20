import { createRequire } from 'module';
const require = createRequire(import.meta.url);
const napi = require('snarky-crypto');

// FIELD-REP COMPAT SHIM — Pallas Poseidon's field is Pallas.BaseField = Fp
// (= VestaScalarField in snarky-crypto naming). After the Pasta.js flip,
// PS hands us bigints here; snarky-crypto still wants `External<Fp>`.
const toFp = (b) => napi.vestaScalarfieldFromBigint(b);
const fromFp = (e) => napi.vestaScalarfieldToBigint(e);

// ============================================================================
// PALLAS POSEIDON FFI
// ============================================================================

export function sbox(x) {
    return fromFp(napi.pallasPoseidonSbox(toFp(x)));
}

export function applyMds(state) {
    return napi.pallasPoseidonApplyMds(state.map(toFp)).map(fromFp);
}

export function fullRound(state) {
    return function(roundIndex) {
        return napi.pallasPoseidonFullRound(state.map(toFp), roundIndex).map(fromFp);
    };
}

export function getRoundConstants(roundIndex) {
    return napi.pallasPoseidonGetRoundConstants(roundIndex).map(fromFp);
}

export function getNumRounds() {
    return napi.pallasPoseidonGetNumRounds();
}

export function getMdsMatrix() {
    return napi.pallasPoseidonGetMdsMatrix().map((row) => row.map(fromFp));
}

export function hash(inputs) {
    return fromFp(napi.pallasPoseidonHash(inputs.map(toFp)));
}
