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

pub type Bn254ProvingKeyExternal = External<Vec<u8>>;
pub type Bn254VerifyingKeyExternal = External<Vec<u8>>;
pub type Bn254ProofExternal = External<Vec<u8>>;

#[napi(object)]
#[derive(Debug)]
pub struct R1CSDimensions {
    #[napi(js_name = "numConstraints")]
    pub num_constraints: u32,
    #[napi(js_name = "numVariables")]
    pub num_variables: u32,
    #[napi(js_name = "numInputs")]
    pub num_inputs: u32,
}

// Helper to convert sparse matrices to R1CS circuit
struct R1CSCircuit {
    dimensions: R1CSDimensions,
    matrix_a: Vec<Vec<(u32, Fr)>>,
    matrix_b: Vec<Vec<(u32, Fr)>>,
    matrix_c: Vec<Vec<(u32, Fr)>>,
    witness: Option<Vec<Fr>>,
    public_inputs: Option<Vec<Fr>>,
}

impl R1CSCircuit {
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
            witness: None,
            public_inputs: None,
        }
    }

    fn with_witness(mut self, witness: Vec<Fr>, public_inputs: Vec<Fr>) -> Self {
        self.witness = Some(witness);
        self.public_inputs = Some(public_inputs);
        self
    }
}

impl ConstraintSynthesizer<Fr> for R1CSCircuit {
    fn generate_constraints(
        self,
        cs: ConstraintSystemRef<Fr>,
    ) -> std::result::Result<(), SynthesisError> {
        // Allocate public inputs
        let mut variables: Vec<Variable> = Vec::new();

        // Variable 0 is always the constant 1
        variables.push(Variable::One);

        // Allocate public input variables
        if let Some(ref public_inputs) = self.public_inputs {
            for &value in public_inputs.iter() {
                let var = cs.new_input_variable(|| Ok(value))?;
                variables.push(var);
            }
        } else {
            // Just allocate without values for setup
            for _i in 0..self.dimensions.num_inputs {
                let var = cs.new_input_variable(|| Ok(Fr::from(0u32)))?;
                variables.push(var);
            }
        }

        // Allocate witness variables
        let remaining_vars = self.dimensions.num_variables as usize - variables.len();
        if let Some(ref witness) = self.witness {
            for &value in witness.iter() {
                let var = cs.new_witness_variable(|| Ok(value))?;
                variables.push(var);
            }
        } else {
            // Just allocate without values for setup
            for _i in 0..remaining_vars {
                let var = cs.new_witness_variable(|| Ok(Fr::from(0u32)))?;
                variables.push(var);
            }
        }

        // Generate R1CS constraints from sparse matrices
        for constraint_idx in 0..self.dimensions.num_constraints as usize {
            // Build linear combinations for A, B, C
            let mut lc_a = lc!();
            let mut lc_b = lc!();
            let mut lc_c = lc!();

            // Add terms for matrix A
            if constraint_idx < self.matrix_a.len() {
                for &(var_idx, coeff) in &self.matrix_a[constraint_idx] {
                    if (var_idx as usize) < variables.len() {
                        lc_a += (coeff, variables[var_idx as usize]);
                    }
                }
            }

            // Add terms for matrix B
            if constraint_idx < self.matrix_b.len() {
                for &(var_idx, coeff) in &self.matrix_b[constraint_idx] {
                    if (var_idx as usize) < variables.len() {
                        lc_b += (coeff, variables[var_idx as usize]);
                    }
                }
            }

            // Add terms for matrix C
            if constraint_idx < self.matrix_c.len() {
                for &(var_idx, coeff) in &self.matrix_c[constraint_idx] {
                    if (var_idx as usize) < variables.len() {
                        lc_c += (coeff, variables[var_idx as usize]);
                    }
                }
            }

            // Enforce the R1CS constraint: A * B = C
            cs.enforce_constraint(lc_a, lc_b, lc_c)?;
        }

        Ok(())
    }
}

#[napi]
pub fn bn254_setup(
    dimensions: R1CSDimensions,
    sparse_a: Vec<Vec<(u32, &Bn254FieldExternal)>>,
    sparse_b: Vec<Vec<(u32, &Bn254FieldExternal)>>,
    sparse_c: Vec<Vec<(u32, &Bn254FieldExternal)>>,
    seed: u32,
) -> Result<(Bn254ProvingKeyExternal, Bn254VerifyingKeyExternal)> {
    // Convert sparse matrices to Fr
    let matrix_a: Vec<Vec<(u32, Fr)>> = sparse_a
        .into_iter()
        .map(|row| {
            row.into_iter()
                .map(|(idx, field_ext)| (idx, **field_ext))
                .collect()
        })
        .collect::<Vec<_>>();

    let matrix_b: Vec<Vec<(u32, Fr)>> = sparse_b
        .into_iter()
        .map(|row| {
            row.into_iter()
                .map(|(idx, field_ext)| (idx, **field_ext))
                .collect()
        })
        .collect::<Vec<_>>();

    let matrix_c: Vec<Vec<(u32, Fr)>> = sparse_c
        .into_iter()
        .map(|row| {
            row.into_iter()
                .map(|(idx, field_ext)| (idx, **field_ext))
                .collect()
        })
        .collect::<Vec<_>>();

    // Create the circuit
    let circuit = R1CSCircuit::new(dimensions, matrix_a, matrix_b, matrix_c);

    // Setup RNG
    let mut rng = ChaCha20Rng::seed_from_u64(seed as u64);

    // Generate proving and verifying keys
    let (pk, vk) = Groth16::<ark_bn254::Bn254>::circuit_specific_setup(circuit, &mut rng)
        .map_err(|e| Error::new(Status::GenericFailure, format!("Setup failed: {e}")))?;

    // Serialize keys to bytes
    let mut pk_bytes = Vec::new();
    pk.serialize_compressed(&mut pk_bytes).map_err(|e| {
        Error::new(
            Status::GenericFailure,
            format!("Failed to serialize proving key: {e}"),
        )
    })?;
    let mut vk_bytes = Vec::new();
    vk.serialize_compressed(&mut vk_bytes).map_err(|e| {
        Error::new(
            Status::GenericFailure,
            format!("Failed to serialize verifying key: {e}"),
        )
    })?;

    Ok((External::new(pk_bytes), External::new(vk_bytes)))
}

#[napi]
#[allow(clippy::too_many_arguments)]
pub fn bn254_prove(
    pk: &Bn254ProvingKeyExternal,
    dimensions: R1CSDimensions,
    sparse_a: Vec<Vec<(u32, &Bn254FieldExternal)>>,
    sparse_b: Vec<Vec<(u32, &Bn254FieldExternal)>>,
    sparse_c: Vec<Vec<(u32, &Bn254FieldExternal)>>,
    witness: Vec<&Bn254FieldExternal>,
    public_inputs: Vec<&Bn254FieldExternal>,
    seed: u32,
) -> Result<Bn254ProofExternal> {
    // Convert sparse matrices to Fr
    let matrix_a: Vec<Vec<(u32, Fr)>> = sparse_a
        .into_iter()
        .map(|row| {
            row.into_iter()
                .map(|(idx, field_ext)| (idx, **field_ext))
                .collect()
        })
        .collect::<Vec<_>>();

    let matrix_b: Vec<Vec<(u32, Fr)>> = sparse_b
        .into_iter()
        .map(|row| {
            row.into_iter()
                .map(|(idx, field_ext)| (idx, **field_ext))
                .collect()
        })
        .collect::<Vec<_>>();

    let matrix_c: Vec<Vec<(u32, Fr)>> = sparse_c
        .into_iter()
        .map(|row| {
            row.into_iter()
                .map(|(idx, field_ext)| (idx, **field_ext))
                .collect()
        })
        .collect::<Vec<_>>();

    // Convert witness and public inputs
    let witness_fr: Vec<Fr> = witness
        .into_iter()
        .map(|field_ext| **field_ext) // Dereference External<Fr>
        .collect();

    let public_inputs_fr: Vec<Fr> = public_inputs
        .into_iter()
        .map(|field_ext| **field_ext) // Dereference External<Fr>
        .collect();

    // Deserialize proving key
    let pk =
        ProvingKey::<ark_bn254::Bn254>::deserialize_compressed(&**pk as &[u8]).map_err(|e| {
            Error::new(
                Status::GenericFailure,
                format!("Failed to deserialize proving key: {e}"),
            )
        })?;

    // Create circuit with witness
    let circuit = R1CSCircuit::new(dimensions, matrix_a, matrix_b, matrix_c)
        .with_witness(witness_fr, public_inputs_fr.clone());

    // Setup RNG
    let mut rng = ChaCha20Rng::seed_from_u64(seed as u64);

    // Generate proof
    let proof = Groth16::<ark_bn254::Bn254>::prove(&pk, circuit, &mut rng)
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

#[napi]
pub fn bn254_verify(
    vk: &Bn254VerifyingKeyExternal,
    proof: &Bn254ProofExternal,
    public_inputs: Vec<&Bn254FieldExternal>,
) -> bool {
    // Convert public inputs
    let public_inputs_fr: Vec<Fr> = public_inputs
        .into_iter()
        .map(|field_ext| **field_ext) // Dereference External<Fr>
        .collect();

    // Deserialize verifying key and proof
    let vk_result = VerifyingKey::<ark_bn254::Bn254>::deserialize_compressed(&**vk as &[u8]);
    let proof_result = Proof::<ark_bn254::Bn254>::deserialize_compressed(&**proof as &[u8]);

    match (vk_result, proof_result) {
        (Ok(vk), Ok(proof)) => {
            // Verify proof, return false on error
            Groth16::<ark_bn254::Bn254>::verify(&vk, &public_inputs_fr, &proof).unwrap_or_default()
        }
        _ => false,
    }
}

#[napi]
pub fn bn254_circuit_check_satisfaction(
    dimensions: R1CSDimensions,
    sparse_a: Vec<Vec<(u32, &Bn254FieldExternal)>>,
    sparse_b: Vec<Vec<(u32, &Bn254FieldExternal)>>,
    sparse_c: Vec<Vec<(u32, &Bn254FieldExternal)>>,
    witness: Vec<&Bn254FieldExternal>,
    public_inputs: Vec<&Bn254FieldExternal>,
) -> bool {
    // Convert sparse matrices to Fr
    let matrix_a: Vec<Vec<(u32, Fr)>> = sparse_a
        .into_iter()
        .map(|row| {
            row.into_iter()
                .map(|(idx, field_ext)| (idx, **field_ext))
                .collect()
        })
        .collect::<Vec<_>>();

    let matrix_b: Vec<Vec<(u32, Fr)>> = sparse_b
        .into_iter()
        .map(|row| {
            row.into_iter()
                .map(|(idx, field_ext)| (idx, **field_ext))
                .collect()
        })
        .collect::<Vec<_>>();

    let matrix_c: Vec<Vec<(u32, Fr)>> = sparse_c
        .into_iter()
        .map(|row| {
            row.into_iter()
                .map(|(idx, field_ext)| (idx, **field_ext))
                .collect()
        })
        .collect::<Vec<_>>();

    // Convert witness and public inputs
    let witness_fr: Vec<Fr> = witness
        .into_iter()
        .map(|field_ext| **field_ext) // Dereference External<Fr>
        .collect();

    let public_inputs_fr: Vec<Fr> = public_inputs
        .into_iter()
        .map(|field_ext| **field_ext) // Dereference External<Fr>
        .collect();

    // Check satisfaction by manually verifying R1CS constraints
    // Create full assignment vector: [1, public_inputs..., witness...]
    let mut assignment = vec![Fr::from(1u32)]; // constant 1
    assignment.extend_from_slice(&public_inputs_fr);
    assignment.extend_from_slice(&witness_fr);

    // Check each constraint: A * B = C
    for constraint_idx in 0..dimensions.num_constraints as usize {
        let mut a_val = Fr::from(0u32);
        let mut b_val = Fr::from(0u32);
        let mut c_val = Fr::from(0u32);

        // Evaluate A
        if constraint_idx < matrix_a.len() {
            for &(var_idx, coeff) in &matrix_a[constraint_idx] {
                if (var_idx as usize) < assignment.len() {
                    a_val += coeff * assignment[var_idx as usize];
                }
            }
        }

        // Evaluate B
        if constraint_idx < matrix_b.len() {
            for &(var_idx, coeff) in &matrix_b[constraint_idx] {
                if (var_idx as usize) < assignment.len() {
                    b_val += coeff * assignment[var_idx as usize];
                }
            }
        }

        // Evaluate C
        if constraint_idx < matrix_c.len() {
            for &(var_idx, coeff) in &matrix_c[constraint_idx] {
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
