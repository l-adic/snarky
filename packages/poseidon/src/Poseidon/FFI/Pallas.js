import { createRequire } from 'module';
const require = createRequire(import.meta.url);
const napi = require('snarky-crypto');

// ============================================================================
// PALLAS POSEIDON FFI
// ============================================================================

export function sbox(x) {
    return napi.pallasPoseidonSbox(x);
}

export function applyMds(state) {
    return napi.pallasPoseidonApplyMds(state);
}

export function fullRound(state) {
    return function(roundIndex) {
        return napi.pallasPoseidonFullRound(state, roundIndex);
    };
}

export function getRoundConstants(roundIndex) {
    return napi.pallasPoseidonGetRoundConstants(roundIndex);
}

export function getNumRounds() {
    return napi.pallasPoseidonGetNumRounds();
}

export function getMdsMatrix() {
    return napi.pallasPoseidonGetMdsMatrix();
}

export function hash(inputs) {
    return napi.pallasPoseidonHash(inputs);
}