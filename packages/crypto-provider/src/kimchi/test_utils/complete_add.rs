use napi::bindgen_prelude::*;
use napi_derive::napi;

use crate::pasta::types::{PallasBaseField, VestaBaseField};
use kimchi::circuits::gate::{CircuitGate, GateType};
use kimchi::circuits::wires::COLUMNS;

#[napi]
pub fn verify_pallas_complete_add(witness_row: Vec<&External<PallasBaseField>>) -> bool {
    let gate = CircuitGate::new(GateType::CompleteAdd, Default::default(), vec![]);

    let mut witness: [Vec<PallasBaseField>; COLUMNS] = Default::default();
    for i in 0..COLUMNS {
        witness[i] = Vec::new();
    }

    for (col_idx, field_ext) in witness_row.into_iter().enumerate().take(15) {
        witness[col_idx] = vec![**field_ext];
    }

    for col_idx in 15..COLUMNS {
        witness[col_idx] = vec![PallasBaseField::from(0u32)];
    }

    gate.verify_complete_add(0, &witness).is_ok()
}

#[napi]
pub fn verify_vesta_complete_add(witness_row: Vec<&External<VestaBaseField>>) -> bool {
    let gate = CircuitGate::new(GateType::CompleteAdd, Default::default(), vec![]);

    let mut witness: [Vec<VestaBaseField>; COLUMNS] = Default::default();
    for i in 0..COLUMNS {
        witness[i] = Vec::new();
    }

    for (col_idx, field_ext) in witness_row.into_iter().enumerate().take(15) {
        witness[col_idx] = vec![**field_ext];
    }

    for col_idx in 15..COLUMNS {
        witness[col_idx] = vec![VestaBaseField::from(0u32)];
    }

    gate.verify_complete_add(0, &witness).is_ok()
}
