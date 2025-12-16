use ark_ff::Zero;
use bulletproofs::circuit::{prove, verify};
use napi::bindgen_prelude::*;
use napi_derive::napi;
use rand::SeedableRng;
use rand_chacha::ChaCha8Rng;
use spongefish::domain_separator;

use crate::pallas::scalar_field::FieldExternal as PallasFieldExternal;
use crate::pasta::types::{PallasScalarField, VestaScalarField};
use crate::vesta::scalar_field::FieldExternal as VestaFieldExternal;

use crate::bulletproofs_types::*;

fn is_power_of_2(n: usize) -> bool {
    n > 0 && (n & (n - 1)) == 0
}

fn validate_power_of_2(n: usize, context: &str) {
    if !is_power_of_2(n) {
        panic!("{context}: expected power of 2, got {n}");
    }
}

// Sparse circuit representation types
#[napi(object)]
pub struct CircuitDimensions {
    pub n: u32, // multiplication gates (must be power of 2)
    pub m: u32, // public inputs
    pub q: u32, // constraints
}

#[napi]
pub fn pallas_crs_create(n: u32, seed: u32) -> PallasCrsExternal {
    let mut rng = ChaCha8Rng::seed_from_u64(seed as u64);
    let crs = CRS::rand(n as usize, &mut rng);
    External::new(crs)
}

#[napi]
pub fn pallas_crs_size(crs: &PallasCrsExternal) -> u32 {
    crs.size() as u32
}

fn external_array_to_field_vec(arr: Vec<&PallasFieldExternal>) -> Vec<PallasScalarField> {
    arr.into_iter().map(|ext| **ext).collect()
}

// Convert sparse matrix (tuples as 2-element arrays) to dense matrix with specified dimensions
fn sparse_to_dense_matrix(
    sparse_matrix: &Vec<Vec<(u32, &PallasFieldExternal)>>,
    rows: usize,
    cols: usize,
) -> Vec<Vec<PallasScalarField>> {
    let mut dense_matrix = vec![vec![PallasScalarField::from(0u64); cols]; rows];

    for (row_idx, sparse_row) in sparse_matrix.iter().enumerate() {
        if row_idx >= rows {
            break;
        }
        for (idx, val) in sparse_row.iter() {
            if (*idx as usize) < cols {
                dense_matrix[row_idx][*idx as usize] = ***val;
            }
        }
    }

    dense_matrix
}

// Convert sparse vector (tuples as 2-element arrays) to dense vector
fn sparse_to_dense_vector(
    sparse_vector: &Vec<(u32, &PallasFieldExternal)>,
    size: usize,
) -> Vec<PallasScalarField> {
    let mut dense_vector = vec![PallasScalarField::from(0u64); size];

    for (idx, val) in sparse_vector.iter() {
        if (*idx as usize) < size {
            dense_vector[*idx as usize] = ***val;
        }
    }

    dense_vector
}

#[napi]
pub fn pallas_witness_create(
    a_l: Vec<&PallasFieldExternal>,
    a_r: Vec<&PallasFieldExternal>,
    a_o: Vec<&PallasFieldExternal>,
    v: Vec<&PallasFieldExternal>,
    seed: u32,
) -> PallasWitnessExternal {
    let mut rng = ChaCha8Rng::seed_from_u64(seed as u64);

    let a_l = external_array_to_field_vec(a_l);
    let a_r = external_array_to_field_vec(a_r);
    let a_o = external_array_to_field_vec(a_o);
    let v = external_array_to_field_vec(v);

    let witness_len = a_l.len();
    validate_power_of_2(witness_len, "Pallas witness length");

    let witness = Witness::new(a_l, a_r, a_o, v, &mut rng);
    External::new(witness)
}

#[napi]
pub fn pallas_witness_size(witness: &PallasWitnessExternal) -> u32 {
    witness.size() as u32
}

#[napi]
pub fn pallas_statement_create(
    crs: &PallasCrsExternal,
    witness: &PallasWitnessExternal,
) -> PallasStatementExternal {
    let statement = Statement::new(crs, witness);
    External::new(statement)
}

// Circuit creation function using tuples (represented as 2-element arrays)
#[napi]
pub fn pallas_circuit_create(
    dimensions: CircuitDimensions,
    sparse_w_l: Vec<Vec<(u32, &PallasFieldExternal)>>, // q constraints × sparse entries
    sparse_w_r: Vec<Vec<(u32, &PallasFieldExternal)>>,
    sparse_w_o: Vec<Vec<(u32, &PallasFieldExternal)>>,
    sparse_w_v: Vec<Vec<(u32, &PallasFieldExternal)>>,
    sparse_c: Vec<(u32, &PallasFieldExternal)>, // sparse vector
) -> PallasCircuitExternal {
    // Validate that n is already a power of 2
    let n = dimensions.n as usize;
    validate_power_of_2(n, "Pallas circuit dimension n");

    // Convert sparse format to dense matrices
    let w_l = sparse_to_dense_matrix(&sparse_w_l, dimensions.q as usize, n);
    let w_r = sparse_to_dense_matrix(&sparse_w_r, dimensions.q as usize, n);
    let w_o = sparse_to_dense_matrix(&sparse_w_o, dimensions.q as usize, n);
    let w_v = sparse_to_dense_matrix(&sparse_w_v, dimensions.q as usize, dimensions.m as usize);
    let c = sparse_to_dense_vector(&sparse_c, dimensions.q as usize);

    let circuit = Circuit::new(w_l, w_r, w_o, w_v, c);
    External::new(circuit)
}

#[napi]
pub fn pallas_circuit_n(circuit: &PallasCircuitExternal) -> u32 {
    circuit.n() as u32
}

#[napi]
pub fn pallas_circuit_q(circuit: &PallasCircuitExternal) -> u32 {
    circuit.q() as u32
}

#[napi]
pub fn pallas_circuit_is_satisfied_by(
    circuit: &PallasCircuitExternal,
    witness: &PallasWitnessExternal,
) -> bool {
    circuit.is_satisfied_by(witness)
}

#[napi]
pub fn pallas_prove(
    crs: &PallasCrsExternal,
    circuit: &PallasCircuitExternal,
    witness: &PallasWitnessExternal,
    seed: u32,
) -> PallasProofExternal {
    let mut rng = ChaCha8Rng::seed_from_u64(seed as u64);
    let statement = Statement::new(crs, witness);
    let domain_separator = domain_separator!("snarky-circuit-proof").instance(&statement.v);
    let mut prover_state = domain_separator.std_prover();
    let proof = prove(&mut prover_state, crs, circuit, witness, &mut rng);
    External::new(proof)
}

#[napi]
pub fn pallas_verify(
    crs: &PallasCrsExternal,
    circuit: &PallasCircuitExternal,
    statement: &PallasStatementExternal,
    proof: &PallasProofExternal,
) -> bool {
    let domain_separator = domain_separator!("snarky-circuit-proof").instance(&statement.v);
    let mut verifier_state = domain_separator.std_verifier(proof);
    let result = verify(&mut verifier_state, crs, circuit, statement);
    result.is_ok()
}

// Vesta curve functions

#[napi]
pub fn vesta_crs_create(n: u32, seed: u32) -> VestaCrsExternal {
    let mut rng = ChaCha8Rng::seed_from_u64(seed as u64);
    let crs = CRS::rand(n as usize, &mut rng);
    External::new(crs)
}

#[napi]
pub fn vesta_crs_size(crs: &VestaCrsExternal) -> u32 {
    crs.size() as u32
}

fn external_array_to_vesta_field_vec(arr: Vec<&VestaFieldExternal>) -> Vec<VestaScalarField> {
    arr.into_iter().map(|f| **f).collect()
}

#[napi]
pub fn vesta_witness_create(
    a_l: Vec<&VestaFieldExternal>,
    a_r: Vec<&VestaFieldExternal>,
    a_o: Vec<&VestaFieldExternal>,
    v: Vec<&VestaFieldExternal>,
    seed: u32,
) -> VestaWitnessExternal {
    let mut rng = ChaCha8Rng::seed_from_u64(seed as u64);

    let a_l = external_array_to_vesta_field_vec(a_l);
    let a_r = external_array_to_vesta_field_vec(a_r);
    let a_o = external_array_to_vesta_field_vec(a_o);
    let v = external_array_to_vesta_field_vec(v);

    // Validate witness vectors are already power of 2 and same length
    let witness_len = a_l.len();
    validate_power_of_2(witness_len, "Vesta witness length");

    if a_r.len() != witness_len || a_o.len() != witness_len {
        panic!(
            "Vesta witness vectors must be same length: a_l={}, a_r={}, a_o={}",
            a_l.len(),
            a_r.len(),
            a_o.len()
        );
    }

    let witness = Witness::new(a_l, a_r, a_o, v, &mut rng);
    External::new(witness)
}

#[napi]
pub fn vesta_witness_size(witness: &VestaWitnessExternal) -> u32 {
    witness.a_l.len() as u32
}

#[napi]
pub fn vesta_statement_create(
    crs: &VestaCrsExternal,
    witness: &VestaWitnessExternal,
) -> VestaStatementExternal {
    let statement = Statement::new(crs, witness);
    External::new(statement)
}

// Circuit creation function using tuples (represented as 2-element arrays)
#[napi]
pub fn vesta_circuit_create(
    dimensions: CircuitDimensions,
    sparse_w_l: Vec<Vec<(u32, &VestaFieldExternal)>>, // q constraints × sparse entries
    sparse_w_r: Vec<Vec<(u32, &VestaFieldExternal)>>,
    sparse_w_o: Vec<Vec<(u32, &VestaFieldExternal)>>,
    sparse_w_v: Vec<Vec<(u32, &VestaFieldExternal)>>, // auxiliary weights
    sparse_c: Vec<(u32, &VestaFieldExternal)>,        // sparse vector
) -> VestaCircuitExternal {
    let n = dimensions.n as usize;
    let q = dimensions.q as usize;
    let m = dimensions.m as usize;

    // Validate that n is already a power of 2
    validate_power_of_2(n, "Vesta circuit dimension n");

    // Helper function to convert sparse representation to dense matrix
    let sparse_to_dense = |sparse_matrix: Vec<Vec<(u32, &VestaFieldExternal)>>,
                           rows: usize,
                           cols: usize|
     -> Vec<Vec<VestaScalarField>> {
        let mut dense = vec![vec![VestaScalarField::zero(); cols]; rows];
        for (row_idx, sparse_row) in sparse_matrix.into_iter().enumerate() {
            if row_idx < rows {
                for (col_idx, field_ref) in sparse_row {
                    let col = col_idx as usize;
                    if col < cols {
                        dense[row_idx][col] = **field_ref;
                    }
                }
            }
        }
        dense
    };

    // Helper function to convert sparse vector to dense vector
    let sparse_vec_to_dense =
        |sparse_vec: Vec<(u32, &VestaFieldExternal)>, size: usize| -> Vec<VestaScalarField> {
            let mut dense = vec![VestaScalarField::zero(); size];
            for (idx, field_ref) in sparse_vec {
                let i = idx as usize;
                if i < size {
                    dense[i] = **field_ref;
                }
            }
            dense
        };

    // Convert sparse matrices to dense format for bulletproof library
    let w_l = sparse_to_dense(sparse_w_l, q, n);
    let w_r = sparse_to_dense(sparse_w_r, q, n);
    let w_o = sparse_to_dense(sparse_w_o, q, n);
    let w_v = sparse_to_dense(sparse_w_v, q, m);
    let c = sparse_vec_to_dense(sparse_c, q);

    let circuit = Circuit::new(w_l, w_r, w_o, w_v, c);
    External::new(circuit)
}

#[napi]
pub fn vesta_circuit_n(circuit: &VestaCircuitExternal) -> u32 {
    circuit.w_l.first().map(|row| row.len()).unwrap_or(0) as u32
}

#[napi]
pub fn vesta_circuit_q(circuit: &VestaCircuitExternal) -> u32 {
    circuit.w_l.len() as u32
}

#[napi]
pub fn vesta_circuit_is_satisfied_by(
    circuit: &VestaCircuitExternal,
    witness: &VestaWitnessExternal,
) -> bool {
    circuit.is_satisfied_by(witness)
}

#[napi]
pub fn vesta_prove(
    crs: &VestaCrsExternal,
    circuit: &VestaCircuitExternal,
    witness: &VestaWitnessExternal,
    seed: u32,
) -> VestaProofExternal {
    let mut rng = ChaCha8Rng::seed_from_u64(seed as u64);
    let statement = Statement::new(crs, witness);
    let domain_separator = domain_separator!("snarky-circuit-proof").instance(&statement.v);
    let mut prover_state = domain_separator.std_prover();
    let proof = prove(&mut prover_state, crs, circuit, witness, &mut rng);

    External::new(proof)
}

#[napi]
pub fn vesta_verify(
    crs: &VestaCrsExternal,
    circuit: &VestaCircuitExternal,
    statement: &VestaStatementExternal,
    proof: &VestaProofExternal,
) -> bool {
    let domain_separator = domain_separator!("snarky-circuit-proof").instance(&statement.v);
    let mut verifier_state = domain_separator.std_verifier(proof);
    let result = verify(&mut verifier_state, crs, circuit, statement);
    result.is_ok()
}
