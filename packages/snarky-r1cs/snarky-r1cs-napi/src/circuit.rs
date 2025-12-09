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


#[napi]
pub fn pallas_circuit_create(
    w_l: Vec<Vec<&PallasFieldExternal>>,
    w_r: Vec<Vec<&PallasFieldExternal>>,
    w_o: Vec<Vec<&PallasFieldExternal>>,
    w_v: Vec<Vec<&PallasFieldExternal>>,
    c: Vec<&PallasFieldExternal>,
) -> PallasCircuitExternal {
    let w_l = external_matrix_to_field_matrix(w_l);
    let w_r = external_matrix_to_field_matrix(w_r);
    let w_o = external_matrix_to_field_matrix(w_o);
    let w_v = external_matrix_to_field_matrix(w_v);
    let c = external_array_to_field_vec(c);
    
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