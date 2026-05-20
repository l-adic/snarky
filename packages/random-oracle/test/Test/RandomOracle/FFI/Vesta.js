import { createRequire } from 'module';
const require = createRequire(import.meta.url);
const napi = require('snarky-crypto');

// Test-only FFI: thin wrappers around Rust Poseidon/Sponge for Vesta
// Used to verify PureScript implementations match Rust exactly.
//
// FIELD-REP COMPAT SHIM — Vesta.BaseField = Fq (= PallasScalarField).
const toFq = (b) => napi.pallasScalarfieldFromBigint(b);
const fromFq = (e) => napi.pallasScalarfieldToBigint(e);

export function permute(state) {
    return napi.vestaPoseidonPermute(state.map(toFq)).map(fromFq);
}

export function spongeCreate() {
    return napi.vestaSpongeCreate();
}

export function spongeAbsorb(sponge) {
    return function(input) {
        return function() {
            napi.vestaSpongeAbsorb(sponge, toFq(input));
        };
    };
}

export function spongeSqueeze(sponge) {
    return function() {
        return fromFq(napi.vestaSpongeSqueeze(sponge));
    };
}
