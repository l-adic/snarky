import { createRequire } from 'module';
const require = createRequire(import.meta.url);
const napi = require('snarky-crypto');

// Test-only FFI: thin wrappers around Rust Poseidon/Sponge for Pallas
// Used to verify PureScript implementations match Rust exactly

export function permute(state) {
    return napi.pallasPoseidonPermute(state);
}

export function spongeCreate() {
    return napi.pallasSpongeCreate();
}

export function spongeAbsorb(sponge) {
    return function(input) {
        return function() {
            napi.pallasSpongeAbsorb(sponge, input);
        };
    };
}

export function spongeSqueeze(sponge) {
    return function() {
        return napi.pallasSpongeSqueeze(sponge);
    };
}
