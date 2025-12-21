// Complete addition gate verification for Pasta curves

use napi::bindgen_prelude::*;
use napi_derive::napi;

use crate::pasta::types::{PallasBaseField, VestaBaseField};
use kimchi::circuits::gate::{CircuitGate, GateType};
use kimchi::circuits::wires::COLUMNS;

#[napi]
pub fn verify_pallas_complete_add(witness_row: Vec<&External<PallasBaseField>>) -> bool {
    let gate = CircuitGate::new(GateType::CompleteAdd, Default::default(), vec![]);
    
    let mut witness: [Vec<PallasBaseField>; COLUMNS] = Default::default();
    // Initialize all columns with empty vectors
    for i in 0..COLUMNS {
        witness[i] = Vec::new();
    }
    
    let witness_row_len = witness_row.len();
    
    // Fill the first 15 columns with our witness data, pad with zeros if needed
    for (col_idx, field_ext) in witness_row.into_iter().enumerate().take(15) {
        witness[col_idx] = vec![**field_ext];
    }
    // Fill remaining AddComplete columns (if any) with zero
    for col_idx in witness_row_len..15 {
        if col_idx < COLUMNS {
            witness[col_idx] = vec![PallasBaseField::from(0u32)];
        }
    }
    // Fill any remaining witness columns with zeros
    for col_idx in 15..COLUMNS {
        witness[col_idx] = vec![PallasBaseField::from(0u32)];
    }
    
    gate.verify_complete_add(0, &witness).is_ok()
}

#[napi]
pub fn verify_vesta_complete_add(witness_row: Vec<&External<VestaBaseField>>) -> bool {
    let gate = CircuitGate::new(GateType::CompleteAdd, Default::default(), vec![]);
    
    let mut witness: [Vec<VestaBaseField>; COLUMNS] = Default::default();
    // Initialize all columns with empty vectors
    for i in 0..COLUMNS {
        witness[i] = Vec::new();
    }
    
    let witness_row_len = witness_row.len();
    
    // Fill the first 15 columns with our witness data, pad with zeros if needed
    for (col_idx, field_ext) in witness_row.into_iter().enumerate().take(15) {
        witness[col_idx] = vec![**field_ext];
    }
    // Fill remaining AddComplete columns (if any) with zero
    for col_idx in witness_row_len..15 {
        if col_idx < COLUMNS {
            witness[col_idx] = vec![VestaBaseField::from(0u32)];
        }
    }
    // Fill any remaining witness columns with zeros
    for col_idx in 15..COLUMNS {
        witness[col_idx] = vec![VestaBaseField::from(0u32)];
    }
    
    gate.verify_complete_add(0, &witness).is_ok()
}