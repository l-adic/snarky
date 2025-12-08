use ark_pallas::{Projective, Fr as PallasFr};
use bulletproofs::circuit::types::{Circuit, Statement, Witness, CRS};
use bulletproofs::circuit::{prove, verify};
use spongefish::{ProverState, VerifierState};
use napi::bindgen_prelude::*;
use napi_derive::napi;
use rand::SeedableRng;
use rand_chacha::ChaCha8Rng;

use curves_napi::pallas::scalar_field::FieldExternal as PallasFieldExternal;

pub type PallasCrsExternal = External<CRS<Projective>>;

pub type PallasWitnessExternal = External<Witness<PallasFr>>;

pub type PallasStatementExternal = External<Statement<Projective>>;

pub type PallasCircuitExternal = External<Circuit<PallasFr>>;

pub type PallasProofExternal = External<Vec<u8>>;

// CRS Functions for Pallas
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
) -> Result<PallasWitnessExternal> {
    let mut rng = ChaCha8Rng::seed_from_u64(seed as u64);
    
    let a_l = external_array_to_field_vec(a_l);
    let a_r = external_array_to_field_vec(a_r);
    let a_o = external_array_to_field_vec(a_o);
    let v = external_array_to_field_vec(v);
    
    // Debug: Print Rust witness dimensions
    println!("=== RUST WITNESS DEBUG ===");
    println!("Rust Witness - a_l length: {}", a_l.len());
    println!("Rust Witness - a_r length: {}", a_r.len());
    println!("Rust Witness - a_o length: {}", a_o.len());
    println!("Rust Witness - v length: {}", v.len());
    
    // Validate that a_l ⊙ a_r = a_o
    for i in 0..a_l.len() {
        if a_l[i] * a_r[i] != a_o[i] {
            return Err(Error::from_reason(
                "Invalid witness: a_l[i] * a_r[i] != a_o[i]",
            ));
        }
    }
    
    let witness = Witness::new(a_l, a_r, a_o, v, &mut rng);
    Ok(External::new(witness))
}

#[napi]
pub fn pallas_witness_size(witness: &PallasWitnessExternal) -> u32 {
    witness.size() as u32
}

// Statement Functions for Pallas
#[napi]
pub fn pallas_statement_create(
    crs: &PallasCrsExternal,
    witness: &PallasWitnessExternal,
) -> PallasStatementExternal {
    let statement = Statement::new(&**crs, &**witness);
    External::new(statement)
}

// Circuit Functions for Pallas
#[napi]
pub fn pallas_circuit_create(
    w_l: Vec<Vec<&PallasFieldExternal>>,
    w_r: Vec<Vec<&PallasFieldExternal>>,
    w_o: Vec<Vec<&PallasFieldExternal>>,
    w_v: Vec<Vec<&PallasFieldExternal>>,
    c: Vec<&PallasFieldExternal>,
) -> Result<PallasCircuitExternal> {
    let w_l = external_matrix_to_field_matrix(w_l);
    let w_r = external_matrix_to_field_matrix(w_r);
    let w_o = external_matrix_to_field_matrix(w_o);
    let w_v = external_matrix_to_field_matrix(w_v);
    let c = external_array_to_field_vec(c);
    
    let circuit = Circuit::new(w_l, w_r, w_o, w_v, c);
    
    // Debug: Print Rust circuit dimensions
    println!("=== RUST CIRCUIT DEBUG ===");
    println!("Rust Circuit - q (constraints): {}", circuit.q());
    println!("Rust Circuit - n (variables): {}", circuit.n());
    
    Ok(External::new(circuit))
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
    let result = circuit.is_satisfied_by(&**witness);
    println!("Rust circuit satisfaction result: {}", result);
    
    // Debug matrix values to compare with PureScript
    println!("=== RUST MATRIX DEBUG ===");
    if !circuit.w_l.is_empty() && !circuit.w_l[0].is_empty() {
        println!("First constraint w_l row: {:?}", &circuit.w_l[0][..std::cmp::min(5, circuit.w_l[0].len())]);
    }
    if !witness.a_l.is_empty() {
        println!("witness.a_l first 3 values: {:?}", &witness.a_l[..std::cmp::min(3, witness.a_l.len())]);
    }
    println!("witness.v: {:?}", witness.v);
    
    result
}

// Prove Functions for Pallas
#[napi]
pub fn pallas_prove(
    crs: &PallasCrsExternal,
    circuit: &PallasCircuitExternal,
    witness: &PallasWitnessExternal,
    seed: u32,
) -> PallasProofExternal {
    let mut rng = ChaCha8Rng::seed_from_u64(seed as u64);
    println!("=== RUST PROVE DEBUG ===");
    println!("Rust Prove - circuit q: {}", circuit.q());
    println!("Rust Prove - circuit n: {}", circuit.n());
    println!("Rust Prove - witness size: {}", witness.size());
    
    // Create statement from witness and CRS
    let statement = Statement::new(&**crs, &**witness);
    
    // Create domain separator and prover state using spongefish
    use spongefish::domain_separator;
    let domain_separator = domain_separator!("snarky-circuit-proof").instance(&statement.v);
    let mut prover_state = domain_separator.std_prover();
    
    let proof = prove(&mut prover_state, &**crs, &**circuit, &**witness, &mut rng);
    println!("Rust Prove - success, proof size: {}", proof.len());
    External::new(proof)
}

// Verify Functions for Pallas
#[napi]
pub fn pallas_verify(
    crs: &PallasCrsExternal,
    circuit: &PallasCircuitExternal,
    statement: &PallasStatementExternal,
    proof: &PallasProofExternal,
) -> bool {
    println!("=== RUST VERIFY DEBUG ===");
    println!("Rust Verify - circuit q: {}", circuit.q());
    println!("Rust Verify - circuit n: {}", circuit.n());
    println!("Rust Verify - proof size: {}", proof.len());
    
    // Create domain separator and verifier state with proof
    use spongefish::domain_separator;
    let domain_separator = domain_separator!("snarky-circuit-proof").instance(&statement.v);
    let mut verifier_state = domain_separator.std_verifier(&**proof);
    
    match verify(&mut verifier_state, &**crs, &**circuit, &**statement) {
        Ok(_) => {
            println!("Rust Verify - success");
            true
        }
        Err(e) => {
            println!("Rust Verify - failed: {:?}", e);
            false
        }
    }
}