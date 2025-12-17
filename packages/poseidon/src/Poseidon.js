import { createRequire } from 'module';
const require = createRequire(import.meta.url);
const napi = require('snarky-crypto');

// ============================================================================
// PALLAS POSEIDON FUNCTIONS
// ============================================================================

// Primitive operations
export function _pallasPoseidonSbox(x) {
    return napi.pallasPoseidonSbox(x);
}

export function _pallasPoseidonApplyMds(state) {
    return napi.pallasPoseidonApplyMds(state);
}

export function _pallasPoseidonFullRound(state) {
    return function(roundIndex) {
        return napi.pallasPoseidonFullRound(state, roundIndex);
    };
}

export function _pallasPoseidonGetRoundConstants(roundIndex) {
    return napi.pallasPoseidonGetRoundConstants(roundIndex);
}

export function _pallasPoseidonGetNumRounds() {
    return napi.pallasPoseidonGetNumRounds();
}

export function _pallasPoseidonGetMdsMatrix() {
    return napi.pallasPoseidonGetMdsMatrix();
}

// High-level hash functions
export function _pallasPoseidonHash(inputs) {
    return napi.pallasPoseidonHash(inputs);
}


// ============================================================================
// VESTA POSEIDON FUNCTIONS
// ============================================================================

// Primitive operations
export function _vestaPoseidonSbox(x) {
    return napi.vestaPoseidonSbox(x);
}

export function _vestaPoseidonApplyMds(state) {
    return napi.vestaPoseidonApplyMds(state);
}

export function _vestaPoseidonFullRound(state) {
    return function(roundIndex) {
        return napi.vestaPoseidonFullRound(state, roundIndex);
    };
}

export function _vestaPoseidonGetRoundConstants(roundIndex) {
    return napi.vestaPoseidonGetRoundConstants(roundIndex);
}

export function _vestaPoseidonGetNumRounds() {
    return napi.vestaPoseidonGetNumRounds();
}

export function _vestaPoseidonGetMdsMatrix() {
    return napi.vestaPoseidonGetMdsMatrix();
}

// High-level hash functions
export function _vestaPoseidonHash(inputs) {
    return napi.vestaPoseidonHash(inputs);
}

