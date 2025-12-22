use napi::bindgen_prelude::*;
use napi_derive::napi;

use crate::pasta::types::{PallasGroup, PallasScalarField, VestaGroup, VestaScalarField};
use kimchi::circuits::gate::{CircuitGate, GateType};
use kimchi::circuits::wires::{Wire, COLUMNS};

pub struct PallasPoseidonVerifier {
    gates: Vec<CircuitGate<PallasScalarField>>,
}

pub struct VestaPoseidonVerifier {
    gates: Vec<CircuitGate<VestaScalarField>>,
}

#[napi]
pub fn make_pallas_poseidon_verifier(
    round_constants: Vec<Vec<&External<PallasScalarField>>>,
    first_row: u32,
    last_row: u32,
) -> External<PallasPoseidonVerifier> {
    let round_constants_converted: Vec<Vec<PallasScalarField>> = round_constants
        .into_iter()
        .map(|row| row.into_iter().map(|field_ext| **field_ext).collect())
        .collect();

    let first_wire_array = Wire::for_row(first_row as usize);
    let last_wire_array = Wire::for_row(last_row as usize);

    let (gates, _next_row) = CircuitGate::create_poseidon_gadget(
        0,
        [first_wire_array, last_wire_array],
        &round_constants_converted,
    );

    let verifier = PallasPoseidonVerifier { gates };

    External::new(verifier)
}

#[napi]
pub fn make_vesta_poseidon_verifier(
    round_constants: Vec<Vec<&External<VestaScalarField>>>,
    first_row: u32,
    last_row: u32,
) -> External<VestaPoseidonVerifier> {
    let round_constants_converted: Vec<Vec<VestaScalarField>> = round_constants
        .into_iter()
        .map(|row| row.into_iter().map(|field_ext| **field_ext).collect())
        .collect();

    let first_wire_array = Wire::for_row(first_row as usize);
    let last_wire_array = Wire::for_row(last_row as usize);

    let (gates, _next_row) = CircuitGate::create_poseidon_gadget(
        0,
        [first_wire_array, last_wire_array],
        &round_constants_converted,
    );

    let verifier = VestaPoseidonVerifier { gates };

    External::new(verifier)
}

#[napi]
pub fn verify_pallas_poseidon_gadget(
    verifier: &External<PallasPoseidonVerifier>,
    witness_matrix: Vec<Vec<&External<PallasScalarField>>>,
) -> bool {
    let mut witness: [Vec<PallasScalarField>; COLUMNS] = Default::default();

    for column in witness.iter_mut().take(COLUMNS) {
        *column = Vec::new();
    }

    for row_data in witness_matrix {
        for (col_idx, field_ext) in row_data.into_iter().enumerate().take(15) {
            witness[col_idx].push(**field_ext);
        }
    }

    for (gate_idx, gate) in verifier.gates.iter().enumerate() {
        if gate.typ == GateType::Poseidon
            && gate
                .verify_poseidon::<PallasGroup>(gate_idx, &witness)
                .is_err()
        {
            return false;
        }
    }

    true
}

#[napi]
pub fn verify_vesta_poseidon_gadget(
    verifier: &External<VestaPoseidonVerifier>,
    witness_matrix: Vec<Vec<&External<VestaScalarField>>>,
) -> bool {
    let mut witness: [Vec<VestaScalarField>; COLUMNS] = Default::default();

    for column in witness.iter_mut().take(COLUMNS) {
        *column = Vec::new();
    }

    for row_data in witness_matrix {
        for (col_idx, field_ext) in row_data.into_iter().enumerate().take(15) {
            witness[col_idx].push(**field_ext);
        }
    }

    for (gate_idx, gate) in verifier.gates.iter().enumerate() {
        if gate.typ == GateType::Poseidon
            && gate
                .verify_poseidon::<VestaGroup>(gate_idx, &witness)
                .is_err()
        {
            return false;
        }
    }

    true
}
