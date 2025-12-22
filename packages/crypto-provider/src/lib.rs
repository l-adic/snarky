// Unified crypto-provider that consolidates curves, bulletproofs, and groth16 functionality
// This replaces the separate NAPI crates with a single unified crate

use napi::bindgen_prelude::*;
use napi_derive::napi;

// ============================================================================
// CURVES MODULE - Basic curve operations and field arithmetic
// ============================================================================

pub mod bn254;

mod bigint;

// Pasta curves with conditional backend support
#[cfg(any(feature = "arkworks", feature = "mina-curves-backend"))]
pub mod pasta;

// Re-export pasta functions for backward compatibility
#[cfg(any(feature = "arkworks", feature = "mina-curves-backend"))]
pub use pasta::*;

// ============================================================================
// BULLETPROOFS MODULE - Zero-knowledge proofs using bulletproofs
// ============================================================================

pub mod bulletproofs_circuit;
pub mod bulletproofs_types;

// Re-export bulletproofs functionality
pub use bulletproofs_circuit::*;
pub use bulletproofs_types::*;

#[napi]
pub fn bulletproofs_init() -> Result<()> {
    Ok(())
}

// ============================================================================
// GROTH16 MODULE - Zero-knowledge proofs using Groth16
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

// External types for NAPI
pub type Bn254ProvingKeyExternal = External<(ProvingKey<ark_bn254::Bn254>, R1CSDimensions)>;
pub type Bn254VerifyingKeyExternal = External<VerifyingKey<ark_bn254::Bn254>>;
pub type Bn254ProofExternal = External<Vec<u8>>;
pub type Bn254CircuitExternal = External<R1CSConstraints>;
pub type Bn254WitnessExternal = External<R1CSWitness>;

#[napi(object)]
#[derive(Debug, Clone)]
pub struct R1CSDimensions {
    #[napi(js_name = "numConstraints")]
    pub num_constraints: u32,
    #[napi(js_name = "numVariables")]
    pub num_variables: u32,
    #[napi(js_name = "numInputs")]
    pub num_inputs: u32,
}

pub struct R1CSConstraints {
    dimensions: R1CSDimensions,
    matrix_a: Vec<Vec<(u32, Fr)>>,
    matrix_b: Vec<Vec<(u32, Fr)>>,
    matrix_c: Vec<Vec<(u32, Fr)>>,
    public_input_indices: Vec<u32>,
}

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

#[napi]
pub fn bn254_witness_create(witness: Vec<&Bn254FieldExternal>) -> External<R1CSWitness> {
    let witness_fr: Vec<Fr> = witness.into_iter().map(|field_ext| **field_ext).collect();

    let r1cs_witness = R1CSWitness {
        witness: witness_fr,
    };
    External::new(r1cs_witness)
}

#[napi]
pub fn bn254_circuit_is_satisfied_by(
    circuit: &External<R1CSConstraints>,
    witness: &External<R1CSWitness>,
) -> bool {
    circuit.is_satisfied_by(witness)
}

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
// KIMCHI MODULE - Poseidon hashing and Kimchi gate functionality
// ============================================================================

#[cfg(feature = "mina-curves-backend")]
pub mod kimchi;

#[cfg(feature = "mina-curves-backend")]
pub use kimchi::poseidon::{
    pallas::{
        pallas_poseidon_apply_mds, pallas_poseidon_full_round, pallas_poseidon_get_mds_matrix,
        pallas_poseidon_get_num_rounds, pallas_poseidon_get_round_constants, pallas_poseidon_hash,
        pallas_poseidon_sbox,
    },
    vesta::{
        vesta_poseidon_apply_mds, vesta_poseidon_full_round, vesta_poseidon_get_mds_matrix,
        vesta_poseidon_get_num_rounds, vesta_poseidon_get_round_constants, vesta_poseidon_hash,
        vesta_poseidon_sbox,
    },
};

#[cfg(feature = "mina-curves-backend")]
pub use kimchi::test_utils::{
    verify_pallas_complete_add, verify_pallas_poseidon, verify_vesta_complete_add,
    verify_vesta_poseidon,
};
