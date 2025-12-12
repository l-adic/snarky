use napi::bindgen_prelude::*;
use napi_derive::napi;

// Re-export all curves functionality
pub use curves_napi::*;

// Arkworks imports
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

use curves_napi::bn254::scalar_field::FieldExternal as Bn254FieldExternal;

// External types following bulletproofs pattern
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

// R1CS constraint system (circuit structure only)
pub struct R1CSConstraints {
    dimensions: R1CSDimensions,
    matrix_a: Vec<Vec<(u32, Fr)>>,
    matrix_b: Vec<Vec<(u32, Fr)>>,
    matrix_c: Vec<Vec<(u32, Fr)>>,
}

// Witness data separate from circuit
#[derive(Clone)]
pub struct R1CSWitness {
    witness: Vec<Fr>,
    public_inputs: Vec<Fr>,
}

impl R1CSConstraints {
    fn new(
        dimensions: R1CSDimensions,
        matrix_a: Vec<Vec<(u32, Fr)>>,
        matrix_b: Vec<Vec<(u32, Fr)>>,
        matrix_c: Vec<Vec<(u32, Fr)>>,
    ) -> Self {
        Self {
            dimensions,
            matrix_a,
            matrix_b,
            matrix_c,
        }
    }

    fn is_satisfied_by(&self, witness: &R1CSWitness) -> bool {
        // Manual satisfaction check like in the original code
        let mut assignment = vec![Fr::from(1u32)]; // constant 1
        assignment.extend_from_slice(&witness.public_inputs);
        assignment.extend_from_slice(&witness.witness);

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

            // Check if A * B = C
            if a_val * b_val != c_val {
                return false;
            }
        }

        true
    }
}

impl R1CSWitness {
    fn new(witness: Vec<Fr>, public_inputs: Vec<Fr>) -> Self {
        Self {
            witness,
            public_inputs,
        }
    }
}

// Single R1CS circuit that can work with or without witness values
#[derive(Clone)]
pub struct R1CSCircuit {
    dimensions: R1CSDimensions,
    matrix_a: Vec<Vec<(u32, Fr)>>,
    matrix_b: Vec<Vec<(u32, Fr)>>,
    matrix_c: Vec<Vec<(u32, Fr)>>,
    // Optional witness - None during setup, Some during proving
    witness_values: Option<R1CSWitness>,
}

impl R1CSCircuit {
    fn new_for_setup(constraints: &R1CSConstraints) -> Self {
        Self {
            dimensions: constraints.dimensions.clone(),
            matrix_a: constraints.matrix_a.clone(),
            matrix_b: constraints.matrix_b.clone(),
            matrix_c: constraints.matrix_c.clone(),
            witness_values: None,
        }
    }

    fn new_for_proving(constraints: &R1CSConstraints, witness: &R1CSWitness) -> Self {
        Self {
            dimensions: constraints.dimensions.clone(),
            matrix_a: constraints.matrix_a.clone(),
            matrix_b: constraints.matrix_b.clone(),
            matrix_c: constraints.matrix_c.clone(),
            witness_values: Some(witness.clone()),
        }
    }
}

impl ConstraintSynthesizer<Fr> for R1CSCircuit {
    fn generate_constraints(
        self,
        cs: ConstraintSystemRef<Fr>,
    ) -> std::result::Result<(), SynthesisError> {
        // Allocate variables - same structure regardless of setup vs proving
        let mut variables: Vec<Variable> = Vec::new();

        // Variable 0 is always the constant 1
        variables.push(Variable::One);

        // Allocate public input variables
        for i in 0..self.dimensions.num_inputs {
            let value = if let Some(ref witness) = self.witness_values {
                if i < witness.public_inputs.len() as u32 {
                    witness.public_inputs[i as usize]
                } else {
                    Fr::from(0u32)
                }
            } else {
                Fr::from(0u32) // Dummy value for setup
            };
            let var = cs.new_input_variable(|| Ok(value))?;
            variables.push(var);
        }

        // Allocate witness variables
        let remaining_vars = self.dimensions.num_variables as usize - variables.len();
        for i in 0..remaining_vars {
            let value = if let Some(ref witness) = self.witness_values {
                if i < witness.witness.len() {
                    witness.witness[i]
                } else {
                    Fr::from(0u32)
                }
            } else {
                Fr::from(0u32) // Dummy value for setup
            };
            let var = cs.new_witness_variable(|| Ok(value))?;
            variables.push(var);
        }

        // Generate R1CS constraints from sparse matrices - same regardless of witness values
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

// Convert sparse matrix from external types to internal Fr types
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

// Following bulletproofs pattern: create circuit (constraints only)
#[napi]
pub fn bn254_circuit_create(
    dimensions: R1CSDimensions,
    sparse_a: Vec<Vec<(u32, &Bn254FieldExternal)>>,
    sparse_b: Vec<Vec<(u32, &Bn254FieldExternal)>>,
    sparse_c: Vec<Vec<(u32, &Bn254FieldExternal)>>,
) -> Bn254CircuitExternal {
    let matrix_a = convert_sparse_matrix(sparse_a);
    let matrix_b = convert_sparse_matrix(sparse_b);
    let matrix_c = convert_sparse_matrix(sparse_c);

    let constraints = R1CSConstraints::new(dimensions, matrix_a, matrix_b, matrix_c);
    External::new(constraints)
}

// Following bulletproofs pattern: create witness separately
#[napi]
pub fn bn254_witness_create(
    witness: Vec<&Bn254FieldExternal>,
    public_inputs: Vec<&Bn254FieldExternal>,
) -> Bn254WitnessExternal {
    let witness_fr: Vec<Fr> = witness.into_iter().map(|field_ext| **field_ext).collect();
    let public_inputs_fr: Vec<Fr> = public_inputs
        .into_iter()
        .map(|field_ext| **field_ext)
        .collect();

    let r1cs_witness = R1CSWitness::new(witness_fr, public_inputs_fr);
    External::new(r1cs_witness)
}

// Following bulletproofs pattern: check satisfaction
#[napi]
pub fn bn254_circuit_is_satisfied_by(
    circuit: &Bn254CircuitExternal,
    witness: &Bn254WitnessExternal,
) -> bool {
    circuit.is_satisfied_by(witness)
}

// Setup: create proving and verifying keys from circuit only
#[napi]
pub fn bn254_setup(
    circuit: &Bn254CircuitExternal,
    seed: u32,
) -> Result<(Bn254ProvingKeyExternal, Bn254VerifyingKeyExternal)> {
    // Setup RNG
    let mut rng = ChaCha20Rng::seed_from_u64(seed as u64);

    // Create circuit for setup (no witness values needed)
    let arkworks_circuit = R1CSCircuit::new_for_setup(circuit);

    // Generate proving and verifying keys
    let (pk, vk) = Groth16::<ark_bn254::Bn254>::circuit_specific_setup(arkworks_circuit, &mut rng)
        .map_err(|e| Error::new(Status::GenericFailure, format!("Setup failed: {e}")))?;

    Ok((
        External::new((pk, circuit.dimensions.clone())),
        External::new(vk),
    ))
}

// Prove: create proof using circuit + witness
#[napi]
pub fn bn254_prove(
    pk: &Bn254ProvingKeyExternal,
    circuit: &Bn254CircuitExternal,
    witness: &Bn254WitnessExternal,
    seed: u32,
) -> Result<Bn254ProofExternal> {
    // Setup RNG
    let mut rng = ChaCha20Rng::seed_from_u64(seed as u64);

    // Create circuit for proving (with witness values)
    let arkworks_circuit = R1CSCircuit::new_for_proving(circuit, witness);

    // Generate proof
    let proof = Groth16::<ark_bn254::Bn254>::prove(&pk.0, arkworks_circuit, &mut rng)
        .map_err(|e| Error::new(Status::GenericFailure, format!("Prove failed: {e}")))?;

    // Serialize proof
    let mut proof_bytes = Vec::new();
    proof.serialize_compressed(&mut proof_bytes).map_err(|e| {
        Error::new(
            Status::GenericFailure,
            format!("Failed to serialize proof: {e}"),
        )
    })?;

    Ok(External::new(proof_bytes))
}

// Verify: check proof against verifying key and public inputs
#[napi]
pub fn bn254_verify(
    vk: &Bn254VerifyingKeyExternal,
    proof: &Bn254ProofExternal,
    public_inputs: Vec<&Bn254FieldExternal>,
) -> bool {
    // Convert public inputs
    let public_inputs_fr: Vec<Fr> = public_inputs
        .into_iter()
        .map(|field_ext| **field_ext)
        .collect();

    // Deserialize proof
    let proof_result = Proof::<ark_bn254::Bn254>::deserialize_compressed(proof as &[u8]);

    match proof_result {
        Ok(proof) => {
            // Verify proof, return false on error
            Groth16::<ark_bn254::Bn254>::verify(vk, &public_inputs_fr, &proof).unwrap_or_default()
        }
        _ => false,
    }
}
