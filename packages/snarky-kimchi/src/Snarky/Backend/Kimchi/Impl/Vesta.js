import { createRequire } from 'module';
const require = createRequire(import.meta.url);
const napi = require('snarky-crypto');


export function vestaCircuitGateNew(gateKind) {
    return function(wires) {
        return function(coeffs) {
            return napi.vestaCircuitGateNew(gateKind, wires, coeffs);
        };
    };
}

export function vestaCircuitGateGetWires(gate) {
    return napi.vestaCircuitGateGetWires(gate);
}

export function vestaCircuitGateCoeffCount(gate) {
    return napi.vestaCircuitGateCoeffCount(gate);
}

export function vestaCircuitGateGetCoeff(gate) {
    return function(index) {
        return napi.vestaCircuitGateGetCoeff(gate, index);
    };
}


export function vestaConstraintSystemCreate(gates) {
    return function(publicInputsCount) {
        return napi.vestaConstraintSystemCreate(gates, publicInputsCount);
    };
}

export function vestaWitnessCreate(witnessColumns) {
    return napi.vestaWitnessCreate(witnessColumns);
}

export function vestaCrsLoadFromCache() {
    return napi.vestaCrsLoadFromCache();
}

export function vestaCrsCreate(depth) {
    return napi.vestaSrsCreate(depth);
}

export function vestaCrsSize(crs) {
    return napi.vestaSrsSize(crs)
}

export function vestaProverIndexCreate(cs) {
    return function(endoQ) {
        return function(srs) {
            return napi.vestaProverIndexCreate(cs, endoQ, srs);
        };
    };
}

export const pallasVerifierIndex = (proverIndex) =>
    napi.pallasVerifierIndex(proverIndex);

export function vestaProverIndexVerify(proverIndex) {
    return function(witness) {
        return function(publicInputs) {
            return napi.vestaProverIndexVerify(proverIndex, witness, publicInputs);
        };
    };
}
