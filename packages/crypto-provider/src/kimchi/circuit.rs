// Kimchi circuit building FFI - Wire operations
//
// This module provides NAPI bindings for kimchi Wire and GateWires types
// from proof-systems, following the existing External pattern.

use napi::bindgen_prelude::*;
use napi_derive::napi;

// Import the actual proof-systems types
use kimchi::circuits::wires::{GateWires, Wire, PERMUTS};

// ============================================================================
// EXTERNAL TYPES FOR WIRES
// ============================================================================

pub type WireExternal = External<Wire>;
pub type GateWiresExternal = External<GateWires>;

// ============================================================================
// WIRE FUNCTIONS
// ============================================================================

#[napi]
pub fn wire_new(row: u32, col: u32) -> WireExternal {
    External::new(Wire::new(row as usize, col as usize))
}

#[napi]
pub fn wire_get_row(wire: &WireExternal) -> u32 {
    wire.row as u32
}

#[napi]
pub fn wire_get_col(wire: &WireExternal) -> u32 {
    wire.col as u32
}

// ============================================================================
// GATE WIRES FUNCTIONS (7-element wire array)
// ============================================================================

#[napi]
pub fn gate_wires_new_from_wires(wires: Vec<&WireExternal>) -> Result<GateWiresExternal> {
    if wires.len() != PERMUTS {
        return Err(Error::new(
            Status::InvalidArg,
            format!("Expected {} wires, got {}", PERMUTS, wires.len()),
        ));
    }

    let mut gate_wires = [Wire::new(0, 0); PERMUTS];
    for (i, wire) in wires.iter().enumerate() {
        gate_wires[i] = ***wire;
    }

    Ok(External::new(gate_wires))
}

#[napi]
pub fn gate_wires_get_wire(wires: &GateWiresExternal, col: u32) -> Result<WireExternal> {
    if col as usize >= PERMUTS {
        return Err(Error::new(
            Status::InvalidArg,
            format!("Wire column {} out of bounds, max is {}", col, PERMUTS - 1),
        ));
    }

    let wire = wires[col as usize];
    Ok(External::new(wire))
}
