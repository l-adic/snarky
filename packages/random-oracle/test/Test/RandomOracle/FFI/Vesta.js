import { createRequire } from 'module';
const require = createRequire(import.meta.url);
const napi = require('snarky-crypto');

// Test-only FFI: thin wrappers around Rust Poseidon/Sponge for Vesta
// Used to verify PureScript implementations match Rust exactly

export function permute(state) {
    return napi.vestaPoseidonPermute(state);
}

export function spongeCreate() {
    return napi.vestaSpongeCreate();
}

export function spongeAbsorb(sponge) {
    return function(input) {
        return function() {
            napi.vestaSpongeAbsorb(sponge, input);
        };
    };
}

export function spongeSqueeze(sponge) {
    return function() {
        return napi.vestaSpongeSqueeze(sponge);
    };
}
