import { createRequire } from 'module';
const require = createRequire(import.meta.url);
const napi = require('snarky-crypto');

// Test-only FFI: thin wrappers around Rust Poseidon/Sponge for Pallas
// Used to verify PureScript implementations match Rust exactly.
//
// FIELD-REP COMPAT SHIM — Pallas.BaseField = Fp (= VestaScalarField).
const toFp = (b) => napi.vestaScalarfieldFromBigint(b);
const fromFp = (e) => napi.vestaScalarfieldToBigint(e);

export function permute(state) {
    return napi.pallasPoseidonPermute(state.map(toFp)).map(fromFp);
}

export function spongeCreate() {
    return napi.pallasSpongeCreate();
}

export function spongeAbsorb(sponge) {
    return function(input) {
        return function() {
            napi.pallasSpongeAbsorb(sponge, toFp(input));
        };
    };
}

export function spongeSqueeze(sponge) {
    return function() {
        return fromFp(napi.pallasSpongeSqueeze(sponge));
    };
}
