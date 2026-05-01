import { createRequire } from 'module';
const require = createRequire(import.meta.url);
const napi = require('snarky-crypto');

export function pallasVerifierIndexToSerdeJson(vi) {
    return napi.pallasVerifierIndexToSerdeJson(vi);
}

export function pallasVerifierIndexFromSerdeJson(json) {
    return function (srs) {
        return napi.pallasVerifierIndexFromSerdeJson(json, srs);
    };
}

// Shape kimchi's `FeatureFlags` napi struct from the PS-side flat
// record. `lookup: false` is required for Pickles wrap proofs (kimchi
// supports lookup but Pickles never enables it).
const toNapiFeatureFlags = (flags) => ({
    rangeCheck0: flags.rangeCheck0,
    rangeCheck1: flags.rangeCheck1,
    foreignFieldAdd: flags.foreignFieldAdd,
    foreignFieldMul: flags.foreignFieldMul,
    xor: flags.xor,
    rot: flags.rot,
    lookup: flags.lookup,
});

export function pallasHydrateVerifierIndex(vk) {
    return function (flags) {
        return function (generic) {
            return napi.pallasHydrateVerifierIndex(vk, toNapiFeatureFlags(flags), generic);
        };
    };
}

export function vestaVerifierIndexToSerdeJson(vi) {
    return napi.vestaVerifierIndexToSerdeJson(vi);
}

export function vestaVerifierIndexFromSerdeJson(json) {
    return function (srs) {
        return napi.vestaVerifierIndexFromSerdeJson(json, srs);
    };
}

export function vestaHydrateVerifierIndex(vk) {
    return function (flags) {
        return function (generic) {
            return napi.vestaHydrateVerifierIndex(vk, toNapiFeatureFlags(flags), generic);
        };
    };
}


export function pallasProofToSerdeJson(proof) {
    return napi.pallasProofToSerdeJson(proof);
}

export function pallasProofFromSerdeJson(json) {
    return napi.pallasProofFromSerdeJson(json);
}

export function vestaProofToSerdeJson(proof) {
    return napi.vestaProofToSerdeJson(proof);
}

export function vestaProofFromSerdeJson(json) {
    return napi.vestaProofFromSerdeJson(json);
}
