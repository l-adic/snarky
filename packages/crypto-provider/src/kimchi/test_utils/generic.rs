use napi::bindgen_prelude::*;
use napi_derive::napi;

use crate::pasta::types::{PallasScalarField, VestaScalarField};
use kimchi::circuits::gate::{CircuitGate, GateType};
use kimchi::circuits::wires::{Wire, COLUMNS};

#[napi]
pub fn verify_pallas_generic(
    coefficients: Vec<&External<PallasScalarField>>,
    witness_row: Vec<&External<PallasScalarField>>,
) -> bool {
    let coeffs: Vec<PallasScalarField> = coefficients.into_iter().map(|c| **c).collect();
    let gate = CircuitGate::new(GateType::Generic, Wire::for_row(0), coeffs);

    let mut witness: [Vec<PallasScalarField>; COLUMNS] = Default::default();
    for column in witness.iter_mut() {
        *column = Vec::new();
    }

    for (col_idx, field_ext) in witness_row.into_iter().enumerate().take(15) {
        witness[col_idx] = vec![**field_ext];
    }

    gate.verify_generic(0, &witness, &[]).is_ok()
}

#[napi]
pub fn verify_vesta_generic(
    coefficients: Vec<&External<VestaScalarField>>,
    witness_row: Vec<&External<VestaScalarField>>,
) -> bool {
    let coeffs: Vec<VestaScalarField> = coefficients.into_iter().map(|c| **c).collect();
    let gate = CircuitGate::new(GateType::Generic, Wire::for_row(0), coeffs);

    let mut witness: [Vec<VestaScalarField>; COLUMNS] = Default::default();
    for column in witness.iter_mut() {
        *column = Vec::new();
    }

    for (col_idx, field_ext) in witness_row.into_iter().enumerate().take(15) {
        witness[col_idx] = vec![**field_ext];
    }

    gate.verify_generic(0, &witness, &[]).is_ok()
}
