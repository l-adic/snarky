use ark_ff::PrimeField;
use napi::bindgen_prelude::*;
use napi_derive::napi;

use crate::kimchi::poseidon::{pallas, vesta};
use crate::pasta::types::{PallasGroup, PallasScalarField, VestaGroup, VestaScalarField};
use kimchi::circuits::gate::{CircuitGate, GateType};
use kimchi::circuits::wires::{Wire, COLUMNS};

fn verify_poseidon_impl<F: PrimeField>(
    num_rows: u32,
    witness_matrix: Vec<Vec<&External<F>>>,
    round_constants: Vec<Vec<F>>,
    verify_gate: impl Fn(&CircuitGate<F>, usize, &[Vec<F>; COLUMNS]) -> bool,
) -> bool {
    let mut witness: [Vec<F>; COLUMNS] = Default::default();

    for column in witness.iter_mut().take(COLUMNS) {
        *column = Vec::new();
    }

    for row_data in witness_matrix {
        for (col_idx, field_ext) in row_data.into_iter().enumerate().take(15) {
            witness[col_idx].push(**field_ext);
        }
    }

    let (gates, _) = CircuitGate::create_poseidon_gadget(
        0,
        [Wire::for_row(0), Wire::for_row(num_rows as usize - 1)],
        &round_constants,
    );

    for (gate_idx, gate) in gates.iter().enumerate() {
        if gate.typ == GateType::Poseidon && !verify_gate(gate, gate_idx, &witness) {
            return false;
        }
    }

    true
}

#[napi]
pub fn verify_pallas_poseidon_gadget(
    num_rows: u32,
    witness_matrix: Vec<Vec<&External<PallasScalarField>>>,
) -> bool {
    let num_rounds = vesta::vesta_poseidon_get_num_rounds();
    let round_constants: Vec<Vec<PallasScalarField>> = (0..num_rounds)
        .map(|round_idx| {
            vesta::vesta_poseidon_get_round_constants(round_idx)
                .into_iter()
                .map(|ext| *ext)
                .collect()
        })
        .collect();

    verify_poseidon_impl(
        num_rows,
        witness_matrix,
        round_constants,
        |gate, idx, witness| gate.verify_poseidon::<PallasGroup>(idx, witness).is_ok(),
    )
}

#[napi]
pub fn verify_vesta_poseidon_gadget(
    num_rows: u32,
    witness_matrix: Vec<Vec<&External<VestaScalarField>>>,
) -> bool {
    let num_rounds = pallas::pallas_poseidon_get_num_rounds();
    let round_constants: Vec<Vec<VestaScalarField>> = (0..num_rounds)
        .map(|round_idx| {
            pallas::pallas_poseidon_get_round_constants(round_idx)
                .into_iter()
                .map(|ext| *ext)
                .collect()
        })
        .collect();

    verify_poseidon_impl(
        num_rows,
        witness_matrix,
        round_constants,
        |gate, idx, witness| gate.verify_poseidon::<VestaGroup>(idx, witness).is_ok(),
    )
}
