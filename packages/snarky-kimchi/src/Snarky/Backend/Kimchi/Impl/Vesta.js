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
