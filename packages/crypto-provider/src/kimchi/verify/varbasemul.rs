use ark_std::Zero;
use napi::bindgen_prelude::*;
use napi_derive::napi;

use crate::pasta::types::{PallasScalarField, VestaScalarField};
use kimchi::circuits::gate::{CircuitGate, GateType};
use kimchi::circuits::wires::{Wire, COLUMNS};

#[napi]
pub fn verify_pallas_varbasemul(witness_rows: Vec<Vec<&External<PallasScalarField>>>) -> bool {
    if witness_rows.len() != 2 {
        return false;
    }

    let gate = CircuitGate::new(GateType::VarBaseMul, Wire::for_row(0), vec![]);

    let mut witness: [Vec<PallasScalarField>; COLUMNS] = Default::default();
    for column in witness.iter_mut() {
        column.resize(2, PallasScalarField::zero());
    }

    for (row_idx, row) in witness_rows.iter().enumerate() {
        for (col_idx, field_ext) in row.iter().enumerate().take(COLUMNS) {
            witness[col_idx][row_idx] = ***field_ext;
        }
    }

    gate.verify_vbmul(0, &witness).is_ok()
}

#[napi]
pub fn verify_vesta_varbasemul(witness_rows: Vec<Vec<&External<VestaScalarField>>>) -> bool {
    if witness_rows.len() != 2 {
        return false;
    }

    let gate = CircuitGate::new(GateType::VarBaseMul, Wire::for_row(0), vec![]);

    let mut witness: [Vec<VestaScalarField>; COLUMNS] = Default::default();
    for column in witness.iter_mut() {
        column.resize(2, VestaScalarField::zero());
    }

    for (row_idx, row) in witness_rows.iter().enumerate() {
        for (col_idx, field_ext) in row.iter().enumerate().take(COLUMNS) {
            witness[col_idx][row_idx] = ***field_ext;
        }
    }

    gate.verify_vbmul(0, &witness).is_ok()
}
