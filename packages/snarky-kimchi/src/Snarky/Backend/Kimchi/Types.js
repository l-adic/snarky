// Wires + gate-wires as plain JS objects matching kimchi-napi's
// `#[napi(object)] NapiWire { row: u32, col: u32 }` and
// `#[napi(object)] NapiGateWires { w0..w6: NapiWire }` shapes.
//
// PureScript holds these as opaque foreign types — the previous backing
// was a `napi::External<Wire>` from snarky-crypto. Switching to plain
// objects is wire-compatible with kimchi-napi's gate-vector, which consumes
// `gate.wires` as exactly `{w0..w6}` via `caml_pasta_fp_plonk_gate_vector_add`.

export function wireNew(row) {
    return function(col) {
        return { row, col };
    };
}

export function wireGetRow(wire) {
    return wire.row;
}

export function wireGetCol(wire) {
    return wire.col;
}

export function gateWiresNewFromWires(wires) {
    // `wires` arrives as a JS Array of 7 elements (PureScript `Vector 7 Wire`
    // is an Array at runtime).
    return {
        w0: wires[0],
        w1: wires[1],
        w2: wires[2],
        w3: wires[3],
        w4: wires[4],
        w5: wires[5],
        w6: wires[6],
    };
}

export function gateWiresGetWire(wires) {
    return function(col) {
        return [wires.w0, wires.w1, wires.w2, wires.w3, wires.w4, wires.w5, wires.w6][col];
    };
}
