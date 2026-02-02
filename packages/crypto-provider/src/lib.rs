//! Unified crypto-provider: NAPI bindings for elliptic curve cryptography.
//!
//! This crate provides Node.js bindings (via NAPI-RS) for cryptographic operations
//! used by the PureScript snarky library. It consolidates:
//!
//! - **Curves**: Field arithmetic and group operations for Pasta (Pallas/Vesta) and BN254
//! - **Poseidon**: zkSNARK-friendly hash function with Kimchi-compatible parameters
//! - **Bulletproofs**: Range proofs and inner product arguments
//! - **Groth16**: zkSNARK proving system over BN254
//! - **Kimchi**: Gate verification functions for the Kimchi proof system
//!
//! # Architecture
//!
//! The PureScript code imports this crate's exports as FFI:
//! ```text
//! PureScript (Snarky.Curves.Pasta) → FFI → crypto-provider (Rust/NAPI)
//! ```
//!
//! Field elements and group points are passed as opaque `External<T>` handles
//! that JavaScript/PureScript cannot inspect directly.

use napi::bindgen_prelude::*;
use napi_derive::napi;

// ============================================================================
// CURVES MODULE
// Field arithmetic and elliptic curve group operations.
// ============================================================================

/// BN254 curve (alt_bn128) - used for Groth16 proofs, Ethereum compatibility.
pub mod bn254;

/// BigInt conversion utilities between NAPI, num-bigint, and arkworks.
mod bigint;

/// Pasta curves (Pallas and Vesta) - used for recursive SNARKs in Mina.
pub mod pasta;

// Re-export pasta functions for backward compatibility
pub use pasta::*;

// ============================================================================
// BULLETPROOFS MODULE
// Zero-knowledge proofs using the Bulletproofs protocol.
// Provides range proofs and R1CS constraint system support.
// ============================================================================

/// Bulletproofs circuit definitions and constraint generation.
pub mod bulletproofs_circuit;

/// Bulletproofs type definitions (commitments, proofs, etc).
pub mod bulletproofs_types;

// Re-export bulletproofs functionality
pub use bulletproofs_circuit::*;
pub use bulletproofs_types::*;

/// Initialize the bulletproofs module (no-op, for API consistency).
#[napi]
pub fn bulletproofs_init() -> Result<()> {
    Ok(())
}

// ============================================================================
// GROTH16 MODULE
// zkSNARK proving system using the Groth16 protocol over BN254.
// Provides setup, prove, and verify operations for R1CS circuits.
// ============================================================================

use std::collections::HashSet;

// Arkworks imports for Groth16
use ark_bn254::Fr;
use ark_groth16::{Groth16, Proof, ProvingKey, VerifyingKey};
use ark_relations::{
    lc,
    r1cs::{ConstraintSynthesizer, ConstraintSystemRef, SynthesisError, Variable},
};
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use ark_snark::SNARK;
use ark_std::vec::Vec;
use rand::SeedableRng;
use rand_chacha::ChaCha20Rng;

use crate::bn254::scalar_field::FieldExternal as Bn254FieldExternal;

// External types for NAPI - opaque handles to Groth16 objects
/// Proving key with circuit dimensions (needed for witness validation).
pub type Bn254ProvingKeyExternal = External<(ProvingKey<ark_bn254::Bn254>, R1CSDimensions)>;
/// Verifying key for proof verification.
pub type Bn254VerifyingKeyExternal = External<VerifyingKey<ark_bn254::Bn254>>;
/// Serialized proof bytes.
pub type Bn254ProofExternal = External<Vec<u8>>;
/// R1CS constraint system.
pub type Bn254CircuitExternal = External<R1CSConstraints>;
/// Witness assignment for all variables.
pub type Bn254WitnessExternal = External<R1CSWitness>;

/// Dimensions of an R1CS constraint system.
///
/// Exposed to JavaScript for circuit introspection.
#[napi(object)]
#[derive(Debug, Clone)]
pub struct R1CSDimensions {
    /// Number of constraints (rows in the A, B, C matrices).
    #[napi(js_name = "numConstraints")]
    pub num_constraints: u32,
    /// Total number of variables (including the constant "1" variable).
    #[napi(js_name = "numVariables")]
    pub num_variables: u32,
    /// Number of public inputs.
    #[napi(js_name = "numInputs")]
    pub num_inputs: u32,
}

/// R1CS constraint system in sparse matrix form.
///
/// Constraints are of the form: (A · w) ∘ (B · w) = C · w
/// where w is the witness vector and ∘ is element-wise multiplication.
pub struct R1CSConstraints {
    dimensions: R1CSDimensions,
    /// Sparse A matrix: matrix_a[constraint_idx] = [(var_idx, coeff), ...]
    matrix_a: Vec<Vec<(u32, Fr)>>,
    /// Sparse B matrix.
    matrix_b: Vec<Vec<(u32, Fr)>>,
    /// Sparse C matrix.
    matrix_c: Vec<Vec<(u32, Fr)>>,
    /// Indices of public input variables.
    public_input_indices: Vec<u32>,
}

/// Witness assignment for an R1CS circuit.
///
/// witness[0] must always be 1 (the constant variable).
#[derive(Clone)]
pub struct R1CSWitness {
    witness: Vec<Fr>,
}

impl R1CSConstraints {
    fn new(
        dimensions: R1CSDimensions,
        matrix_a: Vec<Vec<(u32, Fr)>>,
        matrix_b: Vec<Vec<(u32, Fr)>>,
        matrix_c: Vec<Vec<(u32, Fr)>>,
        public_input_indices: Vec<u32>,
    ) -> Self {
        Self {
            dimensions,
            matrix_a,
            matrix_b,
            matrix_c,
            public_input_indices,
        }
    }

    fn is_satisfied_by(&self, witness: &R1CSWitness) -> bool {
        let assignment = &witness.witness;

        for constraint_idx in 0..self.dimensions.num_constraints as usize {
            let mut a_val = Fr::from(0u32);
            let mut b_val = Fr::from(0u32);
            let mut c_val = Fr::from(0u32);

            // Evaluate A
            if constraint_idx < self.matrix_a.len() {
                for &(var_idx, coeff) in &self.matrix_a[constraint_idx] {
                    if (var_idx as usize) < assignment.len() {
                        a_val += coeff * assignment[var_idx as usize];
                    }
                }
            }

            // Evaluate B
            if constraint_idx < self.matrix_b.len() {
                for &(var_idx, coeff) in &self.matrix_b[constraint_idx] {
                    if (var_idx as usize) < assignment.len() {
                        b_val += coeff * assignment[var_idx as usize];
                    }
                }
            }

            // Evaluate C
            if constraint_idx < self.matrix_c.len() {
                for &(var_idx, coeff) in &self.matrix_c[constraint_idx] {
                    if (var_idx as usize) < assignment.len() {
                        c_val += coeff * assignment[var_idx as usize];
                    }
                }
            }

            if a_val * b_val != c_val {
                return false;
            }
        }

        true
    }
}

#[derive(Clone)]
pub struct R1CSCircuit {
    dimensions: R1CSDimensions,
    matrix_a: Vec<Vec<(u32, Fr)>>,
    matrix_b: Vec<Vec<(u32, Fr)>>,
    matrix_c: Vec<Vec<(u32, Fr)>>,
    public_input_indices: Vec<u32>,
    witness: Option<Vec<Fr>>,
}

impl R1CSCircuit {
    fn new_for_setup(constraints: &R1CSConstraints) -> Self {
        Self {
            dimensions: constraints.dimensions.clone(),
            matrix_a: constraints.matrix_a.clone(),
            matrix_b: constraints.matrix_b.clone(),
            matrix_c: constraints.matrix_c.clone(),
            public_input_indices: constraints.public_input_indices.clone(),
            witness: None,
        }
    }

    fn new_for_proving(constraints: &R1CSConstraints, witness: &R1CSWitness) -> Result<Self> {
        if witness.witness.len() != constraints.dimensions.num_variables as usize {
            return Err(Error::new(
                Status::InvalidArg,
                format!(
                    "Expected witness of size {}, got {}",
                    constraints.dimensions.num_variables,
                    witness.witness.len()
                ),
            ));
        }
        if witness.witness[0] != Fr::from(1u32) {
            return Err(Error::new(
                Status::InvalidArg,
                "Expected witness[0] to be 1",
            ));
        }
        Ok(Self {
            dimensions: constraints.dimensions.clone(),
            matrix_a: constraints.matrix_a.clone(),
            matrix_b: constraints.matrix_b.clone(),
            matrix_c: constraints.matrix_c.clone(),
            public_input_indices: constraints.public_input_indices.clone(),
            witness: Some(witness.witness.clone()),
        })
    }
}

impl ConstraintSynthesizer<Fr> for R1CSCircuit {
    fn generate_constraints(
        self,
        cs: ConstraintSystemRef<Fr>,
    ) -> std::result::Result<(), SynthesisError> {
        let public_input_indices = self
            .public_input_indices
            .iter()
            .copied()
            .collect::<HashSet<u32>>();
        let mut variables: Vec<Variable> = Vec::new();
        variables.push(Variable::One);
        for i in 1..self.dimensions.num_variables {
            let value = if let Some(ref witness) = self.witness {
                witness[i as usize]
            } else {
                Fr::from(0u32)
            };
            let var = if public_input_indices.contains(&i) {
                cs.new_input_variable(|| Ok(value))?
            } else {
                cs.new_witness_variable(|| Ok(value))?
            };
            variables.push(var);
        }

        if variables.len() != self.dimensions.num_variables as usize {
            return Err(SynthesisError::Unsatisfiable);
        }

        for constraint_idx in 0..self.dimensions.num_constraints as usize {
            let mut lc_a = lc!();
            let mut lc_b = lc!();
            let mut lc_c = lc!();

            if constraint_idx < self.matrix_a.len() {
                for &(var_idx, coeff) in &self.matrix_a[constraint_idx] {
                    if (var_idx as usize) < variables.len() {
                        lc_a += (coeff, variables[var_idx as usize]);
                    }
                }
            }

            if constraint_idx < self.matrix_b.len() {
                for &(var_idx, coeff) in &self.matrix_b[constraint_idx] {
                    if (var_idx as usize) < variables.len() {
                        lc_b += (coeff, variables[var_idx as usize]);
                    }
                }
            }

            if constraint_idx < self.matrix_c.len() {
                for &(var_idx, coeff) in &self.matrix_c[constraint_idx] {
                    if (var_idx as usize) < variables.len() {
                        lc_c += (coeff, variables[var_idx as usize]);
                    }
                }
            }

            cs.enforce_constraint(lc_a, lc_b, lc_c)?;
        }

        Ok(())
    }
}

fn convert_sparse_matrix(sparse: Vec<Vec<(u32, &Bn254FieldExternal)>>) -> Vec<Vec<(u32, Fr)>> {
    sparse
        .into_iter()
        .map(|row| {
            row.into_iter()
                .map(|(idx, field_ext)| (idx, **field_ext))
                .collect()
        })
        .collect()
}

/// Create an R1CS circuit from sparse constraint matrices.
///
/// Each matrix is represented as a vector of rows, where each row is
/// a vector of (variable_index, coefficient) pairs.
#[napi]
pub fn bn254_circuit_create(
    dimensions: R1CSDimensions,
    sparse_a: Vec<Vec<(u32, &Bn254FieldExternal)>>,
    sparse_b: Vec<Vec<(u32, &Bn254FieldExternal)>>,
    sparse_c: Vec<Vec<(u32, &Bn254FieldExternal)>>,
    public_input_indices: Vec<u32>,
) -> Result<External<R1CSConstraints>> {
    if sparse_a.len() != sparse_b.len() || sparse_b.len() != sparse_c.len() {
        return Err(Error::new(
            Status::InvalidArg,
            format!(
                "Matrix dimension mismatch: A={}, B={}, C={}, expected all equal",
                sparse_a.len(),
                sparse_b.len(),
                sparse_c.len()
            ),
        ));
    }

    if dimensions.num_constraints as usize != sparse_a.len() {
        return Err(Error::new(
            Status::InvalidArg,
            format!(
                "numConstraints {} doesn't match matrix length {}",
                dimensions.num_constraints,
                sparse_a.len()
            ),
        ));
    }

    let matrix_a = convert_sparse_matrix(sparse_a);
    let matrix_b = convert_sparse_matrix(sparse_b);
    let matrix_c = convert_sparse_matrix(sparse_c);

    let constraints = R1CSConstraints::new(
        dimensions,
        matrix_a,
        matrix_b,
        matrix_c,
        public_input_indices,
    );
    Ok(External::new(constraints))
}

/// Create a witness from field element assignments.
///
/// witness[0] must be 1 (the constant variable).
#[napi]
pub fn bn254_witness_create(witness: Vec<&Bn254FieldExternal>) -> External<R1CSWitness> {
    let witness_fr: Vec<Fr> = witness.into_iter().map(|field_ext| **field_ext).collect();

    let r1cs_witness = R1CSWitness {
        witness: witness_fr,
    };
    External::new(r1cs_witness)
}

/// Check if a witness satisfies all R1CS constraints.
///
/// Returns true if (A·w) ∘ (B·w) = C·w for all constraints.
#[napi]
pub fn bn254_circuit_is_satisfied_by(
    circuit: &External<R1CSConstraints>,
    witness: &External<R1CSWitness>,
) -> bool {
    circuit.is_satisfied_by(witness)
}

/// Generate Groth16 proving and verifying keys for a circuit.
///
/// Uses deterministic randomness from the provided seed.
#[napi]
pub fn bn254_setup(
    circuit: &External<R1CSConstraints>,
    seed: u32,
) -> Result<(Bn254ProvingKeyExternal, Bn254VerifyingKeyExternal)> {
    let mut rng = ChaCha20Rng::seed_from_u64(seed as u64);
    let arkworks_circuit = R1CSCircuit::new_for_setup(circuit);
    let (pk, vk) = Groth16::<ark_bn254::Bn254>::circuit_specific_setup(arkworks_circuit, &mut rng)
        .map_err(|e| Error::new(Status::GenericFailure, format!("Setup failed: {e}")))?;

    Ok((
        External::new((pk, circuit.dimensions.clone())),
        External::new(vk),
    ))
}

/// Generate a Groth16 proof for a circuit with a satisfying witness.
///
/// Returns compressed proof bytes.
#[napi]
pub fn bn254_prove(
    pk: &Bn254ProvingKeyExternal,
    circuit: &External<R1CSConstraints>,
    witness: &External<R1CSWitness>,
    seed: u32,
) -> Result<Bn254ProofExternal> {
    let mut rng = ChaCha20Rng::seed_from_u64(seed as u64);
    let arkworks_circuit = R1CSCircuit::new_for_proving(circuit, witness)?;
    let proof = Groth16::<ark_bn254::Bn254>::prove(&pk.0, arkworks_circuit, &mut rng)
        .map_err(|e| Error::new(Status::GenericFailure, format!("Prove failed: {e}")))?;

    let mut proof_bytes = Vec::new();
    proof.serialize_compressed(&mut proof_bytes).map_err(|e| {
        Error::new(
            Status::GenericFailure,
            format!("Failed to serialize proof: {e}"),
        )
    })?;

    Ok(External::new(proof_bytes))
}

/// Verify a Groth16 proof against public inputs.
///
/// Returns true if the proof is valid.
#[napi]
pub fn bn254_verify(
    vk: &Bn254VerifyingKeyExternal,
    proof: &Bn254ProofExternal,
    public_inputs: Vec<&Bn254FieldExternal>,
) -> bool {
    let public_inputs_fr: Vec<Fr> = public_inputs
        .into_iter()
        .map(|field_ext| **field_ext)
        .collect();

    let proof_result = Proof::<ark_bn254::Bn254>::deserialize_compressed(proof as &[u8]);

    match proof_result {
        Ok(proof) => {
            Groth16::<ark_bn254::Bn254>::verify(vk, &public_inputs_fr, &proof).unwrap_or_default()
        }
        _ => false,
    }
}

// ============================================================================
// KIMCHI MODULE
// Poseidon hashing with Kimchi-compatible parameters, plus gate verification
// functions for testing circuit implementations against reference code.
// ============================================================================

/// Kimchi-specific functionality: Poseidon hash, gate verification, linearization.
pub mod kimchi;

pub use kimchi::poseidon::{
    pallas::{
        pallas_domain_prefix_to_field, pallas_init_with_domain, pallas_poseidon_apply_mds,
        pallas_poseidon_full_round, pallas_poseidon_get_mds_matrix, pallas_poseidon_get_num_rounds,
        pallas_poseidon_get_round_constants, pallas_poseidon_hash, pallas_poseidon_permute,
        pallas_poseidon_sbox, pallas_sponge_absorb, pallas_sponge_create, pallas_sponge_squeeze,
    },
    vesta::{
        vesta_domain_prefix_to_field, vesta_init_with_domain, vesta_poseidon_apply_mds,
        vesta_poseidon_full_round, vesta_poseidon_get_mds_matrix, vesta_poseidon_get_num_rounds,
        vesta_poseidon_get_round_constants, vesta_poseidon_hash, vesta_poseidon_permute,
        vesta_poseidon_sbox, vesta_sponge_absorb, vesta_sponge_create, vesta_sponge_squeeze,
    },
};

pub use kimchi::verify::{
    verify_pallas_complete_add, verify_pallas_generic, verify_pallas_poseidon_gadget,
    verify_pallas_varbasemul, verify_vesta_complete_add, verify_vesta_generic,
    verify_vesta_poseidon_gadget, verify_vesta_varbasemul,
};

pub use kimchi::test_linearization::{evaluate_pallas_linearization, evaluate_vesta_linearization};
