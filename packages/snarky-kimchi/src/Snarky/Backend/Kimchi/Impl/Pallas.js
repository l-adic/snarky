import { createRequire } from 'module';
const require = createRequire(import.meta.url);
const napi = require('snarky-crypto');


export function pallasCircuitGateNew(gateKind) {
    return function(wires) {
        return function(coeffs) {
            return napi.pallasCircuitGateNew(gateKind, wires, coeffs);
        };
    };
}

export function pallasCircuitGateGetWires(gate) {
    return napi.pallasCircuitGateGetWires(gate);
}

export function pallasCircuitGateCoeffCount(gate) {
    return napi.pallasCircuitGateCoeffCount(gate);
}

export function pallasCircuitGateGetCoeff(gate) {
    return function(index) {
        return napi.pallasCircuitGateGetCoeff(gate, index);
    };
}


export function pallasConstraintSystemCreate(gates) {
    return function(publicInputsCount) {
        return napi.pallasConstraintSystemCreate(gates, publicInputsCount);
    };
}

export function pallasWitnessCreate(witnessColumns) {
    return napi.pallasWitnessCreate(witnessColumns);
}

export function pallasCrsLoadFromCache() {
    return napi.pallasCrsLoadFromCache();
}

export function pallasProverIndexCreate(cs) {
    return function(endoQ) {
        return function(srs) {
            return napi.pallasProverIndexCreate(cs, endoQ, srs);
        };
    };
}

export function pallasProverIndexVerify(proverIndex) {
    return function(witness) {
        return function(publicInputs) {
            return napi.pallasProverIndexVerify(proverIndex, witness, publicInputs);
        };
    };
}
