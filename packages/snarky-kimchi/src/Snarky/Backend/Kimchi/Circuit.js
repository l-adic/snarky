import { createRequire } from 'module';
const require = createRequire(import.meta.url);
const napi = require('snarky-crypto');

// ============================================================================
// WIRE FUNCTIONS
// ============================================================================

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

// ============================================================================
// GATE WIRES FUNCTIONS (7-element wire array)
// ============================================================================

export function gateWiresNewFromWires(wires) {
    return napi.gateWiresNewFromWires(wires);
}

export function gateWiresGetWire(wires) {
    return function(col) {
        return napi.gateWiresGetWire(wires, col);
    };
}


