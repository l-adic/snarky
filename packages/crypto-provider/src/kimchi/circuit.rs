// Kimchi circuit building FFI - Wire operations
//
// This module provides NAPI bindings for kimchi Wire and GateWires types
// from proof-systems, following the existing External pattern.

use napi::bindgen_prelude::*;
use napi_derive::napi;

// Import the actual proof-systems types
use kimchi::circuits::constraints::ConstraintSystem;
use kimchi::circuits::gate::{CircuitGate, GateType};
use kimchi::circuits::wires::{GateWires, Wire, COLUMNS, PERMUTS};

// Import field types from our pasta module
use super::super::pasta::pallas::scalar_field::FieldExternal as PallasFieldExternal;
use super::super::pasta::types::{PallasScalarField, VestaScalarField};
use super::super::pasta::vesta::scalar_field::FieldExternal as VestaFieldExternal;

pub type WireExternal = External<Wire>;
pub type GateWiresExternal = External<GateWires>;
pub type PallasCircuitGateExternal = External<CircuitGate<PallasScalarField>>;
pub type VestaCircuitGateExternal = External<CircuitGate<VestaScalarField>>;
pub type PallasConstraintSystemExternal = External<ConstraintSystem<PallasScalarField>>;
pub type VestaConstraintSystemExternal = External<ConstraintSystem<VestaScalarField>>;
pub type PallasWitnessExternal = External<[Vec<PallasScalarField>; COLUMNS]>;
pub type VestaWitnessExternal = External<[Vec<VestaScalarField>; COLUMNS]>;

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

fn purescript_gate_kind_to_rust_gate_type(gate_kind: &str) -> Result<GateType> {
    match gate_kind {
        "Zero" => Ok(GateType::Zero),
        "GenericPlonkGate" => Ok(GateType::Generic),
        "PoseidonGate" => Ok(GateType::Poseidon),
        "AddCompleteGate" => Ok(GateType::CompleteAdd),
        "VarBaseMul" => Ok(GateType::VarBaseMul),
        "EndoMul" => Ok(GateType::EndoMul),
        "EndoScalar" => Ok(GateType::EndoMulScalar),
        _ => Err(Error::new(
            Status::InvalidArg,
            format!("Invalid PureScript gate kind: '{gate_kind}'. Valid kinds: Zero, GenericPlonkGate, PoseidonGate, AddCompleteGate, VarBaseMul, EndoMul, EndoScalar"),
        )),
    }
}

#[napi]
pub fn pallas_circuit_gate_new(
    gate_kind: String,
    wires: &GateWiresExternal,
    coeffs: Vec<&PallasFieldExternal>,
) -> Result<PallasCircuitGateExternal> {
    let gate_type = purescript_gate_kind_to_rust_gate_type(&gate_kind)?;
    let coeffs_vec: Vec<PallasScalarField> = coeffs.iter().map(|c| ***c).collect();

    let circuit_gate = CircuitGate::new(gate_type, **wires, coeffs_vec);
    Ok(External::new(circuit_gate))
}

#[napi]
pub fn pallas_circuit_gate_get_wires(gate: &PallasCircuitGateExternal) -> GateWiresExternal {
    External::new(gate.wires)
}

#[napi]
pub fn pallas_circuit_gate_coeff_count(gate: &PallasCircuitGateExternal) -> u32 {
    gate.coeffs.len() as u32
}

#[napi]
pub fn pallas_circuit_gate_get_coeff(
    gate: &PallasCircuitGateExternal,
    index: u32,
) -> Result<PallasFieldExternal> {
    let coeff = gate.coeffs.get(index as usize).ok_or_else(|| {
        Error::new(
            Status::InvalidArg,
            format!("Coefficient index {index} out of bounds"),
        )
    })?;
    Ok(External::new(*coeff))
}

#[napi]
pub fn vesta_circuit_gate_new(
    gate_kind: String,
    wires: &GateWiresExternal,
    coeffs: Vec<&VestaFieldExternal>,
) -> Result<VestaCircuitGateExternal> {
    let gate_type = purescript_gate_kind_to_rust_gate_type(&gate_kind)?;
    let coeffs_vec: Vec<VestaScalarField> = coeffs.iter().map(|c| ***c).collect();

    let circuit_gate = CircuitGate::new(gate_type, **wires, coeffs_vec);
    Ok(External::new(circuit_gate))
}

#[napi]
pub fn vesta_circuit_gate_get_wires(gate: &VestaCircuitGateExternal) -> GateWiresExternal {
    External::new(gate.wires)
}

#[napi]
pub fn vesta_circuit_gate_coeff_count(gate: &VestaCircuitGateExternal) -> u32 {
    gate.coeffs.len() as u32
}

#[napi]
pub fn vesta_circuit_gate_get_coeff(
    gate: &VestaCircuitGateExternal,
    index: u32,
) -> Result<VestaFieldExternal> {
    let coeff = gate.coeffs.get(index as usize).ok_or_else(|| {
        Error::new(
            Status::InvalidArg,
            format!("Coefficient index {index} out of bounds"),
        )
    })?;
    Ok(External::new(*coeff))
}

#[napi]
pub fn pallas_constraint_system_create(
    gates: Vec<&PallasCircuitGateExternal>,
    public_inputs_count: u32,
) -> Result<PallasConstraintSystemExternal> {
    let internal_gates: Vec<CircuitGate<PallasScalarField>> = gates
        .into_iter()
        .map(|gate_ext| (**gate_ext).clone())
        .collect();

    let cs = ConstraintSystem::create(internal_gates)
        .public(public_inputs_count as usize)
        .build()
        .map_err(|e| {
            Error::new(
                Status::GenericFailure,
                format!("Failed to create constraint system: {e}"),
            )
        })?;

    Ok(External::new(cs))
}

#[napi]
pub fn vesta_constraint_system_create(
    gates: Vec<&VestaCircuitGateExternal>,
    public_inputs_count: u32,
) -> Result<VestaConstraintSystemExternal> {
    let internal_gates: Vec<CircuitGate<VestaScalarField>> = gates
        .into_iter()
        .map(|gate_ext| (**gate_ext).clone())
        .collect();

    let cs = ConstraintSystem::create(internal_gates)
        .public(public_inputs_count as usize)
        .build()
        .map_err(|e| {
            Error::new(
                Status::GenericFailure,
                format!("Failed to create constraint system: {e}"),
            )
        })?;

    Ok(External::new(cs))
}

#[napi]
pub fn pallas_witness_create(
    witness_columns: Vec<Vec<&PallasFieldExternal>>,
) -> PallasWitnessExternal {
    let witness: [Vec<PallasScalarField>; COLUMNS] = std::array::from_fn(|i| {
        witness_columns[i]
            .iter()
            .map(|field_ext| ***field_ext)
            .collect()
    });
    External::new(witness)
}

#[napi]
pub fn vesta_witness_create(
    witness_columns: Vec<Vec<&VestaFieldExternal>>,
) -> VestaWitnessExternal {
    let witness: [Vec<VestaScalarField>; COLUMNS] = std::array::from_fn(|i| {
        witness_columns[i]
            .iter()
            .map(|field_ext| ***field_ext)
            .collect()
    });
    External::new(witness)
}
