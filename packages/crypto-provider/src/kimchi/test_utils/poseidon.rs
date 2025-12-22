use napi::bindgen_prelude::*;
use napi_derive::napi;

use crate::pasta::types::{PallasGroup, PallasScalarField, VestaGroup, VestaScalarField};
use kimchi::circuits::gate::{CircuitGate, GateType};
use kimchi::circuits::wires::COLUMNS;

#[napi]
pub fn verify_pallas_poseidon(
    row: Vec<&External<PallasScalarField>>,
    next_row: Vec<&External<PallasScalarField>>,
    coeffs: Vec<&External<PallasScalarField>>,
) -> bool {
    if row.len() != 15 || next_row.len() != 15 {
        println!(
            "Invalid vector lengths: row.len() = {}, next_row.len() = {}",
            row.len(),
            next_row.len()
        );
        return false;
    }

    let coeffs_vec: Vec<PallasScalarField> = coeffs.into_iter().map(|c| **c).collect();
    let gate = CircuitGate::new(GateType::Poseidon, Default::default(), coeffs_vec);

    // Create witness matrix where each column has exactly 2 elements [current_row, next_row]
    let mut witness_vecs: Vec<Vec<PallasScalarField>> = Vec::with_capacity(COLUMNS);

    // Fill first 15 columns with actual data
    for col_idx in 0..15 {
        witness_vecs.push(vec![**row[col_idx], **next_row[col_idx]]);
    }

    // Fill remaining columns with zeros
    for _ in 15..COLUMNS {
        witness_vecs.push(vec![
            PallasScalarField::from(0u32),
            PallasScalarField::from(0u32),
        ]);
    }

    // Convert to fixed-size array
    let witness: [Vec<PallasScalarField>; COLUMNS] = witness_vecs.try_into().unwrap();

    gate.verify_poseidon::<PallasGroup>(0, &witness).is_ok()
}

#[napi]
pub fn verify_vesta_poseidon(
    row: Vec<&External<VestaScalarField>>,
    next_row: Vec<&External<VestaScalarField>>,
    coeffs: Vec<&External<VestaScalarField>>,
) -> bool {
    if row.len() != 15 || next_row.len() != 15 {
        println!(
            "Invalid vector lengths: row.len() = {}, next_row.len() = {}",
            row.len(),
            next_row.len()
        );
        return false;
    }

    let coeffs_vec: Vec<VestaScalarField> = coeffs.into_iter().map(|c| **c).collect();
    let gate = CircuitGate::new(GateType::Poseidon, Default::default(), coeffs_vec);

    // Create witness matrix where each column has exactly 2 elements [current_row, next_row]
    let mut witness_vecs: Vec<Vec<VestaScalarField>> = Vec::with_capacity(COLUMNS);

    // Fill first 15 columns with actual data
    for col_idx in 0..15 {
        witness_vecs.push(vec![**row[col_idx], **next_row[col_idx]]);
    }

    // Fill remaining columns with zeros
    for _ in 15..COLUMNS {
        witness_vecs.push(vec![
            VestaScalarField::from(0u32),
            VestaScalarField::from(0u32),
        ]);
    }

    // Convert to fixed-size array
    let witness: [Vec<VestaScalarField>; COLUMNS] = witness_vecs.try_into().unwrap();

    gate.verify_poseidon::<VestaGroup>(0, &witness).is_ok()
}
