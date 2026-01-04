import { createRequire } from 'module';
const require = createRequire(import.meta.url);
const napi = require('snarky-crypto');


export function wireNew(row) {
    return function(col) {
        return napi.wireNew(row, col);
    };
}

export function wireGetRow(wire) {
    return napi.wireGetRow(wire);
}

export function wireGetCol(wire) {
    return napi.wireGetCol(wire);
}


export function gateWiresNewFromWires(wires) {
    return napi.gateWiresNewFromWires(wires);
}

export function gateWiresGetWire(wires) {
    return function(col) {
        return napi.gateWiresGetWire(wires, col);
    };
}


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



export function pallasConstraintSystemCreate(gates) {
    return function(publicInputsCount) {
        return napi.pallasConstraintSystemCreate(gates, publicInputsCount);
    };
}

export function vestaConstraintSystemCreate(gates) {
    return function(publicInputsCount) {
        return napi.vestaConstraintSystemCreate(gates, publicInputsCount);
    };
}

export function pallasWitnessCreate(witnessColumns) {
    return napi.pallasWitnessCreate(witnessColumns);
}

export function vestaWitnessCreate(witnessColumns) {
    return napi.vestaWitnessCreate(witnessColumns);
}

export function pallasWitnessCreate(witnessColumns) {
    return napi.pallasWitnessCreate(witnessColumns);
}

export function vestaWitnessCreate(witnessColumns) {
    return napi.vestaWitnessCreate(witnessColumns);
}
