import { createRequire } from 'module';
const require = createRequire(import.meta.url);
const napi = require('snarky-crypto');

// ============================================================================
// VESTA POSEIDON FFI
// ============================================================================

export function sbox(x) {
    return napi.vestaPoseidonSbox(x);
}

export function applyMds(state) {
    return napi.vestaPoseidonApplyMds(state);
}

export function fullRound(state) {
    return function(roundIndex) {
        return napi.vestaPoseidonFullRound(state, roundIndex);
    };
}

export function getRoundConstants(roundIndex) {
    return napi.vestaPoseidonGetRoundConstants(roundIndex);
}

export function getNumRounds() {
    return napi.vestaPoseidonGetNumRounds();
}

export function getMdsMatrix() {
    return napi.vestaPoseidonGetMdsMatrix();
}

export function hash(inputs) {
    return napi.vestaPoseidonHash(inputs);
}