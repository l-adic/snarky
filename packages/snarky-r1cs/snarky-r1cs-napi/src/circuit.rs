use ark_pallas::{Projective, Fr as PallasFr};
use bulletproofs::circuit::types::{Circuit, Statement, Witness, CRS};
use bulletproofs::circuit::{prove, verify};
use spongefish::domain_separator;
use napi::bindgen_prelude::*;
use napi_derive::napi;
use rand::SeedableRng;
use rand_chacha::ChaCha8Rng;

use curves_napi::pallas::scalar_field::FieldExternal as PallasFieldExternal;

fn next_power_of_2(n: usize) -> usize {
    if n <= 1 {
        1
    } else {
        let mut power = 1;
        while power < n {
            power *= 2;
        }
        power
    }
}

pub type PallasCrsExternal = External<CRS<Projective>>;
pub type PallasWitnessExternal = External<Witness<PallasFr>>;
pub type PallasStatementExternal = External<Statement<Projective>>;
pub type PallasCircuitExternal = External<Circuit<PallasFr>>;
pub type PallasProofExternal = External<Vec<u8>>;

// Sparse circuit representation types
#[napi(object)]
pub struct CircuitDimensions {
    pub n: u32,  // multiplication gates (will be padded to power of 2)
    pub m: u32,  // public inputs
    pub q: u32,  // constraints
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

fn external_array_to_field_vec(arr: Vec<&PallasFieldExternal>) -> Vec<PallasFr> {
    arr.into_iter().map(|ext| **ext).collect()
}

fn external_matrix_to_field_matrix(matrix: Vec<Vec<&PallasFieldExternal>>) -> Vec<Vec<PallasFr>> {
    matrix
        .into_iter()
        .map(|row| external_array_to_field_vec(row))
        .collect()
}

// Convert sparse matrix (tuples as 2-element arrays) to dense matrix with specified dimensions
fn sparse_to_dense_matrix(
    sparse_matrix: &Vec<Vec<(u32, &PallasFieldExternal)>>,
    rows: usize,
    cols: usize,
) -> Vec<Vec<PallasFr>> {
    let mut dense_matrix = vec![vec![PallasFr::from(0u64); cols]; rows];
    
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
) -> Vec<PallasFr> {
    let mut dense_vector = vec![PallasFr::from(0u64); size];
    
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
    
    let mut a_l = external_array_to_field_vec(a_l);
    let mut a_r = external_array_to_field_vec(a_r);
    let mut a_o = external_array_to_field_vec(a_o);
    let v = external_array_to_field_vec(v);
    
    let current_len = a_l.len();
    let padded_len = next_power_of_2(current_len);
    
    if current_len < padded_len {
        a_l.resize(padded_len, PallasFr::from(0u64));
        a_r.resize(padded_len, PallasFr::from(0u64));
        a_o.resize(padded_len, PallasFr::from(0u64));
    }
    
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
    let statement = Statement::new(&**crs, &**witness);
    External::new(statement)
}


// Circuit creation function using tuples (represented as 2-element arrays)
#[napi]
pub fn pallas_circuit_create(
    dimensions: CircuitDimensions,
    sparse_w_l: Vec<Vec<(u32, &PallasFieldExternal)>>,  // q constraints × sparse entries
    sparse_w_r: Vec<Vec<(u32, &PallasFieldExternal)>>,
    sparse_w_o: Vec<Vec<(u32, &PallasFieldExternal)>>,
    sparse_w_v: Vec<Vec<(u32, &PallasFieldExternal)>>,
    sparse_c: Vec<(u32, &PallasFieldExternal)>,         // sparse vector
) -> PallasCircuitExternal {
    // Pad n to next power of 2 for bulletproof compatibility
    let padded_n = next_power_of_2(dimensions.n as usize);
    
    println!("Creating circuit with dimensions: n={} (padded to {}), m={}, q={}", 
             dimensions.n, padded_n, dimensions.m, dimensions.q);

    // Convert sparse format to dense matrices with padding
    let w_l = sparse_to_dense_matrix(&sparse_w_l, dimensions.q as usize, padded_n);
    let w_r = sparse_to_dense_matrix(&sparse_w_r, dimensions.q as usize, padded_n);
    let w_o = sparse_to_dense_matrix(&sparse_w_o, dimensions.q as usize, padded_n);
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
    circuit.is_satisfied_by(&**witness)
}

#[napi]
pub fn pallas_prove(
    crs: &PallasCrsExternal,
    circuit: &PallasCircuitExternal,
    witness: &PallasWitnessExternal,
    seed: u32,
) -> PallasProofExternal {
    let mut rng = ChaCha8Rng::seed_from_u64(seed as u64);
    let statement = Statement::new(&**crs, &**witness);
    let domain_separator = domain_separator!("snarky-circuit-proof").instance(&statement.v);
    let mut prover_state = domain_separator.std_prover();
    let proof = prove(&mut prover_state, &**crs, &**circuit, &**witness, &mut rng);
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
    let mut verifier_state = domain_separator.std_verifier(&**proof);
    let result = verify(&mut verifier_state, &**crs, &**circuit, &**statement);
    result.is_ok()
}