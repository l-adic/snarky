// Kimchi circuit building FFI - Wire operations
//
// This module provides NAPI bindings for kimchi Wire and GateWires types
// from proof-systems, following the existing External pattern.

use napi::bindgen_prelude::*;
use napi_derive::napi;

// Import the actual proof-systems types
use kimchi::circuits::constraints::ConstraintSystem;
use kimchi::circuits::gate::{CircuitGate, GateType};
use kimchi::circuits::wires::{GateWires, Wire, COLUMNS, PERMUTS};
use kimchi::proof::ProverProof;
use kimchi::prover_index::ProverIndex;
use poly_commitment::commitment::CommitmentCurve;
use poly_commitment::ipa::OpeningProof;
use poly_commitment::{ipa::SRS, precomputed_srs::TestSRS};
use serde;
use std::fs::File;
use std::path::Path;
use std::sync::Arc;

// Import field types from our pasta module
use super::super::pasta::pallas::scalar_field::FieldExternal as PallasFieldExternal;
use super::super::pasta::types::{
    PallasConfig, PallasGroup, PallasScalarField, VestaConfig, VestaGroup, VestaScalarField,
};
use super::super::pasta::vesta::scalar_field::FieldExternal as VestaFieldExternal;
use ark_ff::PrimeField;
use ark_poly::EvaluationDomain;
use kimchi::curve::vesta_endos;
use mina_poseidon::constants::PlonkSpongeConstantsKimchi;
use mina_poseidon::sponge::{DefaultFqSponge, DefaultFrSponge};

pub type WireExternal = External<Wire>;
pub type GateWiresExternal = External<GateWires>;
pub type PallasCircuitGateExternal = External<CircuitGate<PallasScalarField>>;
pub type VestaCircuitGateExternal = External<CircuitGate<VestaScalarField>>;
pub type PallasConstraintSystemExternal = External<ConstraintSystem<PallasScalarField>>;
pub type VestaConstraintSystemExternal = External<ConstraintSystem<VestaScalarField>>;
pub type PallasCRSExternal = External<SRS<super::super::pasta::types::PallasGroup>>;
pub type VestaCRSExternal = External<SRS<super::super::pasta::types::VestaGroup>>;
pub type PallasProverIndexExternal = External<
    ProverIndex<
        super::super::pasta::types::PallasGroup,
        OpeningProof<super::super::pasta::types::PallasGroup>,
    >,
>;
pub type VestaProverIndexExternal = External<
    ProverIndex<
        super::super::pasta::types::VestaGroup,
        OpeningProof<super::super::pasta::types::VestaGroup>,
    >,
>;
pub type PallasProofExternal = External<ProverProof<PallasGroup, OpeningProof<PallasGroup>>>;
pub type VestaProofExternal = External<ProverProof<VestaGroup, OpeningProof<VestaGroup>>>;

// Sponge type aliases for each curve
type VestaBaseSponge = DefaultFqSponge<VestaConfig, PlonkSpongeConstantsKimchi>;
type VestaScalarSponge = DefaultFrSponge<VestaScalarField, PlonkSpongeConstantsKimchi>;
type PallasBaseSponge = DefaultFqSponge<PallasConfig, PlonkSpongeConstantsKimchi>;
type PallasScalarSponge = DefaultFrSponge<PallasScalarField, PlonkSpongeConstantsKimchi>;

// Generic implementations for circuit operations
pub(crate) mod generic {
    use super::*;
    use ark_poly::{EvaluationDomain, Evaluations, Polynomial, Radix2EvaluationDomain};
    use ark_std::{One, Zero};
    use kimchi::curve::KimchiCurve;
    use kimchi::groupmap::GroupMap;
    use poly_commitment::SRS as SRSTrait;

    pub fn circuit_gate_new<F: PrimeField>(
        gate_kind: &str,
        wires: &GateWires,
        coeffs: Vec<F>,
    ) -> Result<CircuitGate<F>> {
        let gate_type = super::purescript_gate_kind_to_rust_gate_type(gate_kind)?;
        Ok(CircuitGate::new(gate_type, *wires, coeffs))
    }

    pub fn constraint_system_create<F: PrimeField>(
        gates: Vec<CircuitGate<F>>,
        public_inputs_count: usize,
    ) -> Result<ConstraintSystem<F>> {
        ConstraintSystem::create(gates)
            .public(public_inputs_count)
            .build()
            .map_err(|e| {
                Error::new(
                    Status::GenericFailure,
                    format!("Failed to create constraint system: {e}"),
                )
            })
    }

    pub fn prover_index_verify<G>(
        prover_index: &ProverIndex<G, OpeningProof<G>>,
        witness: &[Vec<G::ScalarField>; COLUMNS],
        public: &[G::ScalarField],
    ) -> bool
    where
        G: KimchiCurve,
        G::BaseField: PrimeField,
    {
        match prover_index.verify(witness, public) {
            Ok(()) => true,
            Err(e) => {
                eprintln!("Verification failed: {e:?}");
                false
            }
        }
    }

    pub fn witness_evaluations<F: PrimeField>(
        domain: Radix2EvaluationDomain<F>,
        witness_columns: Vec<Vec<F>>,
        zeta: F,
    ) -> Vec<F> {
        let domain_size = domain.size();
        let omega = domain.group_gen();
        let zeta_omega = zeta * omega;

        let mut result = Vec::with_capacity(COLUMNS * 2);
        for col_data in witness_columns.iter().take(COLUMNS) {
            let mut col_vals = col_data.clone();
            col_vals.resize(domain_size, F::zero());
            let poly = Evaluations::from_vec_and_domain(col_vals, domain).interpolate();
            result.push(poly.evaluate(&zeta));
            result.push(poly.evaluate(&zeta_omega));
        }
        result
    }

    pub fn coefficient_evaluations<F: PrimeField>(
        domain: Radix2EvaluationDomain<F>,
        gates: &[CircuitGate<F>],
        zeta: F,
    ) -> Vec<F> {
        let domain_size = domain.size();
        let num_gates = gates.len();
        let coeff_cols = 15usize;

        let mut coeff_columns: Vec<Vec<F>> = vec![vec![F::zero(); num_gates]; coeff_cols];
        for (row, gate) in gates.iter().enumerate() {
            for (col_idx, coeff) in gate.coeffs.iter().enumerate() {
                if col_idx < coeff_cols {
                    coeff_columns[col_idx][row] = *coeff;
                }
            }
        }

        let mut result = Vec::with_capacity(coeff_cols);
        for col_vals in &coeff_columns {
            let mut col_vals = col_vals.clone();
            col_vals.resize(domain_size, F::zero());
            let poly = Evaluations::from_vec_and_domain(col_vals, domain).interpolate();
            result.push(poly.evaluate(&zeta));
        }
        result
    }

    pub fn selector_evaluations<F: PrimeField>(
        domain: Radix2EvaluationDomain<F>,
        gates: &[CircuitGate<F>],
        zeta: F,
    ) -> Vec<F> {
        let domain_size = domain.size();
        let omega = domain.group_gen();
        let zeta_omega = zeta * omega;

        // Order must match Kimchi verifier's column ordering for combined_inner_product
        // See kimchi/src/verifier.rs lines 485-490
        let gate_types = [
            GateType::Generic,
            GateType::Poseidon,
            GateType::CompleteAdd,
            GateType::VarBaseMul,
            GateType::EndoMul,
            GateType::EndoMulScalar,
        ];

        let mut result = Vec::with_capacity(gate_types.len() * 2);
        for gate_type in gate_types.iter() {
            let mut selector: Vec<F> = gates
                .iter()
                .map(|g| {
                    if g.typ == *gate_type {
                        F::from(1u64)
                    } else {
                        F::zero()
                    }
                })
                .collect();
            selector.resize(domain_size, F::zero());
            let poly = Evaluations::from_vec_and_domain(selector, domain).interpolate();
            result.push(poly.evaluate(&zeta));
            result.push(poly.evaluate(&zeta_omega));
        }
        result
    }

    /// Get the 7 domain shift values from a prover index.
    pub fn prover_index_shifts<G: KimchiCurve>(
        prover_index: &ProverIndex<G, OpeningProof<G>>,
    ) -> Vec<G::ScalarField>
    where
        G::BaseField: PrimeField,
    {
        prover_index.cs.shift.to_vec()
    }

    /// Run the Kimchi prover to create a proof.
    pub fn create_proof<G, EFqSponge, EFrSponge>(
        prover_index: &ProverIndex<G, OpeningProof<G>>,
        witness: [Vec<G::ScalarField>; COLUMNS],
    ) -> Result<ProverProof<G, OpeningProof<G>>>
    where
        G: KimchiCurve,
        G::BaseField: PrimeField,
        EFqSponge: Clone + mina_poseidon::FqSponge<G::BaseField, G, G::ScalarField>,
        EFrSponge: kimchi::plonk_sponge::FrSponge<G::ScalarField>,
        kimchi::verifier_index::VerifierIndex<G, OpeningProof<G>>: Clone,
    {
        let group_map = <G as CommitmentCurve>::Map::setup();
        ProverProof::create::<EFqSponge, EFrSponge, _>(
            &group_map,
            witness,
            &[], // no runtime tables
            prover_index,
            &mut rand::rngs::OsRng,
        )
        .map_err(|e| {
            Error::new(
                Status::GenericFailure,
                format!("Proof creation failed: {e:?}"),
            )
        })
    }

    /// Extract witness polynomial evaluations from a proof.
    /// Returns 30 values: 15 columns × 2 points (zeta, zeta*omega).
    pub fn proof_witness_evals<G: KimchiCurve>(
        proof: &ProverProof<G, OpeningProof<G>>,
    ) -> Vec<G::ScalarField>
    where
        G::BaseField: PrimeField,
    {
        let mut result = Vec::with_capacity(COLUMNS * 2);
        for w_eval in &proof.evals.w {
            result.push(w_eval.zeta[0]);
            result.push(w_eval.zeta_omega[0]);
        }
        result
    }

    /// Extract permutation polynomial (z) evaluations from a proof.
    /// Returns 2 values: z(zeta), z(zeta*omega).
    pub fn proof_z_evals<G: KimchiCurve>(
        proof: &ProverProof<G, OpeningProof<G>>,
    ) -> Vec<G::ScalarField>
    where
        G::BaseField: PrimeField,
    {
        vec![proof.evals.z.zeta[0], proof.evals.z.zeta_omega[0]]
    }

    /// Extract sigma polynomial evaluations from a proof.
    /// Returns 12 values: 6 sigma columns × 2 points (zeta, zeta*omega).
    pub fn proof_sigma_evals<G: KimchiCurve>(
        proof: &ProverProof<G, OpeningProof<G>>,
    ) -> Vec<G::ScalarField>
    where
        G::BaseField: PrimeField,
    {
        let mut result = Vec::with_capacity((PERMUTS - 1) * 2);
        for s_eval in &proof.evals.s {
            result.push(s_eval.zeta[0]);
            result.push(s_eval.zeta_omega[0]);
        }
        result
    }

    /// Extract coefficient polynomial evaluations from a proof.
    /// Returns 30 values: 15 coefficient columns × 2 points (zeta, zeta*omega).
    pub fn proof_coefficient_evals<G: KimchiCurve>(
        proof: &ProverProof<G, OpeningProof<G>>,
    ) -> Vec<G::ScalarField>
    where
        G::BaseField: PrimeField,
    {
        let mut result = Vec::with_capacity(COLUMNS * 2);
        for c_eval in &proof.evals.coefficients {
            result.push(c_eval.zeta[0]);
            result.push(c_eval.zeta_omega[0]);
        }
        result
    }

    /// Helper: compute oracles result from prover index and proof.
    /// Returns (verifier_index, oracles_result).
    #[allow(clippy::type_complexity)]
    pub fn compute_oracles<G, EFqSponge, EFrSponge>(
        prover_index: &ProverIndex<G, OpeningProof<G>>,
        proof: &ProverProof<G, OpeningProof<G>>,
        public_input: &[G::ScalarField],
    ) -> Result<(
        kimchi::verifier_index::VerifierIndex<G, OpeningProof<G>>,
        kimchi::oracles::OraclesResult<G, EFqSponge>,
    )>
    where
        G: KimchiCurve,
        G::BaseField: PrimeField,
        EFqSponge: Clone + mina_poseidon::FqSponge<G::BaseField, G, G::ScalarField>,
        EFrSponge: kimchi::plonk_sponge::FrSponge<G::ScalarField>,
        kimchi::verifier_index::VerifierIndex<G, OpeningProof<G>>: Clone,
    {
        let verifier_index = prover_index.verifier_index();

        // Compute public input commitment (same logic as batch_verify)
        let public_comm = {
            let lgr_comm = verifier_index
                .srs()
                .get_lagrange_basis(verifier_index.domain);
            let com: Vec<_> = lgr_comm.iter().take(verifier_index.public).collect();
            if public_input.is_empty() {
                poly_commitment::commitment::PolyComm::new(vec![verifier_index
                    .srs()
                    .blinding_commitment()])
            } else {
                let elm: Vec<_> = public_input.iter().map(|s| -*s).collect();
                let public_comm =
                    poly_commitment::commitment::PolyComm::<G>::multi_scalar_mul(&com, &elm);
                verifier_index
                    .srs()
                    .mask_custom(
                        public_comm.clone(),
                        &public_comm.map(|_| G::ScalarField::one()),
                    )
                    .unwrap()
                    .commitment
            }
        };

        let oracles_result = proof
            .oracles::<EFqSponge, EFrSponge>(&verifier_index, &public_comm, Some(public_input))
            .map_err(|e| {
                Error::new(
                    Status::GenericFailure,
                    format!("Oracle computation failed: {e:?}"),
                )
            })?;

        Ok((verifier_index, oracles_result))
    }

    /// Run the verifier's Fiat-Shamir oracle computation.
    /// Returns 11 values: [alpha, beta, gamma, zeta, ft_eval0, v, u,
    ///                     combined_inner_product, ft_eval1, public_eval_zeta, public_eval_zeta_omega]
    pub fn proof_oracles<G, EFqSponge, EFrSponge>(
        prover_index: &ProverIndex<G, OpeningProof<G>>,
        proof: &ProverProof<G, OpeningProof<G>>,
        public_input: &[G::ScalarField],
    ) -> Result<Vec<G::ScalarField>>
    where
        G: KimchiCurve,
        G::BaseField: PrimeField,
        EFqSponge: Clone + mina_poseidon::FqSponge<G::BaseField, G, G::ScalarField>,
        EFrSponge: kimchi::plonk_sponge::FrSponge<G::ScalarField>,
        kimchi::verifier_index::VerifierIndex<G, OpeningProof<G>>: Clone,
    {
        let (_, oracles_result) =
            compute_oracles::<G, EFqSponge, EFrSponge>(prover_index, proof, public_input)?;

        // public_evals[0] = evaluation at zeta, public_evals[1] = evaluation at zeta*omega
        // Each is a Vec because of chunking, but for non-chunked we just take [0]
        let public_eval_zeta = oracles_result.public_evals[0]
            .first()
            .copied()
            .unwrap_or(G::ScalarField::zero());
        let public_eval_zeta_omega = oracles_result.public_evals[1]
            .first()
            .copied()
            .unwrap_or(G::ScalarField::zero());

        Ok(vec![
            oracles_result.oracles.alpha,
            oracles_result.oracles.beta,
            oracles_result.oracles.gamma,
            oracles_result.oracles.zeta,
            oracles_result.ft_eval0,
            oracles_result.oracles.v,
            oracles_result.oracles.u,
            oracles_result.combined_inner_product,
            proof.ft_eval1,
            public_eval_zeta,
            public_eval_zeta_omega,
        ])
    }

    /// Extract all sponge-derived values needed for the verifier circuit.
    /// Returns (challenges, u_x, u_y, c) where:
    /// - challenges: IPA challenges (endo-mapped, full field elements), d values where d = IPA rounds
    /// - u_x, u_y: U point coordinates from groupMap(squeeze after CIP)
    /// - c: final scalar challenge (128-bit) after absorbing delta
    pub fn proof_bulletproof_challenges<G, EFqSponge, EFrSponge>(
        prover_index: &ProverIndex<G, OpeningProof<G>>,
        proof: &ProverProof<G, OpeningProof<G>>,
        public_input: &[G::ScalarField],
    ) -> Result<(Vec<G::ScalarField>, G::BaseField, G::BaseField, G::ScalarField)>
    where
        G: KimchiCurve,
        G::BaseField: PrimeField,
        EFqSponge: Clone + mina_poseidon::FqSponge<G::BaseField, G, G::ScalarField>,
        EFrSponge: kimchi::plonk_sponge::FrSponge<G::ScalarField>,
        kimchi::verifier_index::VerifierIndex<G, OpeningProof<G>>: Clone,
    {
        use ark_ff::BigInteger;
        use poly_commitment::commitment::CommitmentCurve;

        let (_, oracles_result) =
            compute_oracles::<G, EFqSponge, EFrSponge>(prover_index, proof, public_input)?;

        // Get the sponge from oracles, absorb combined_inner_product, then get challenges
        // This follows the same sequence as SRS::verify in poly-commitment/src/ipa.rs
        let mut fq_sponge = oracles_result.fq_sponge;

        let shifted_cip =
            poly_commitment::commitment::shift_scalar::<G>(oracles_result.combined_inner_product);
        fq_sponge.absorb_fr(&[shifted_cip]);

        // Squeeze u_base and compute U via groupMap
        let u_base = fq_sponge.challenge_fq();
        let group_map = <G as CommitmentCurve>::Map::setup();
        let (u_x, u_y) = group_map.to_group(u_base);

        // Get the challenges using the CANONICAL endomorphism coefficient from the curve
        // IMPORTANT: Use G::endos().1 to match SRS::verify behavior, NOT verifier_index.endo
        let challenges = proof.proof.challenges(&G::endos().1, &mut fq_sponge);

        // Absorb delta and squeeze c
        fq_sponge.absorb_g(&[proof.proof.delta]);
        let c_full = fq_sponge.challenge_fq();

        // Truncate to 128 bits (ScalarChallenge) - matches circuit's endo usage
        let c_bits = c_full.into_bigint().to_bits_le();
        let c_truncated = G::ScalarField::from_bigint(
            <G::ScalarField as ark_ff::PrimeField>::BigInt::from_bits_le(&c_bits[..128]),
        )
        .unwrap();

        Ok((challenges.chal, u_x, u_y, c_truncated))
    }

    /// Verify the opening proof using batch_verify.
    /// Returns true if verification succeeds.
    pub fn verify_opening_proof<G, EFqSponge, EFrSponge>(
        prover_index: &ProverIndex<G, OpeningProof<G>>,
        proof: &ProverProof<G, OpeningProof<G>>,
        public_input: &[G::ScalarField],
    ) -> bool
    where
        G: KimchiCurve,
        G::BaseField: PrimeField,
        EFqSponge: Clone + mina_poseidon::FqSponge<G::BaseField, G, G::ScalarField>,
        EFrSponge: kimchi::plonk_sponge::FrSponge<G::ScalarField>,
        kimchi::verifier_index::VerifierIndex<G, OpeningProof<G>>: Clone,
    {
        eprintln!("DEBUG verify_opening_proof:");
        eprintln!("  proof.proof.sg = {:?}", proof.proof.sg);

        let verifier_index = prover_index.verifier_index();
        let group_map = <G as CommitmentCurve>::Map::setup();

        let context = kimchi::verifier::Context {
            verifier_index: &verifier_index,
            proof,
            public_input,
        };

        match kimchi::verifier::batch_verify::<G, EFqSponge, EFrSponge, OpeningProof<G>>(
            &group_map,
            &[context],
        ) {
            Ok(()) => {
                eprintln!("  batch_verify succeeded!");
                true
            }
            Err(e) => {
                eprintln!("Opening proof verification failed: {e:?}");
                false
            }
        }
    }

    /// Compute b0 = sum_i (evalscale^i * b_poly(challenges, evaluation_points[i]))
    /// For our case with two evaluation points (zeta, zeta_omega):
    ///   b0 = b_poly(challenges, zeta) + evalscale * b_poly(challenges, zeta_omega)
    ///
    /// This is the "b" value used in the IPA verification equation.
    pub fn compute_b0<F: ark_ff::Field>(
        challenges: &[F],
        zeta: F,
        zeta_omega: F,
        evalscale: F,
    ) -> F {
        use poly_commitment::commitment::b_poly;
        b_poly(challenges, zeta) + evalscale * b_poly(challenges, zeta_omega)
    }
}

#[napi]
pub fn wire_new(row: u32, col: u32) -> WireExternal {
    External::new(Wire::new(row as usize, col as usize))
}

#[napi]
pub fn wire_get_row(wire: &WireExternal) -> u32 {
    wire.row as u32
}

#[napi]
pub fn wire_get_col(wire: &WireExternal) -> u32 {
    wire.col as u32
}

#[napi]
pub fn gate_wires_new_from_wires(wires: Vec<&WireExternal>) -> Result<GateWiresExternal> {
    if wires.len() != PERMUTS {
        return Err(Error::new(
            Status::InvalidArg,
            format!("Expected {} wires, got {}", PERMUTS, wires.len()),
        ));
    }

    let mut gate_wires = [Wire::new(0, 0); PERMUTS];
    for (i, wire) in wires.iter().enumerate() {
        gate_wires[i] = ***wire;
    }

    Ok(External::new(gate_wires))
}

#[napi]
pub fn gate_wires_get_wire(wires: &GateWiresExternal, col: u32) -> Result<WireExternal> {
    if col as usize >= PERMUTS {
        return Err(Error::new(
            Status::InvalidArg,
            format!("Wire column {} out of bounds, max is {}", col, PERMUTS - 1),
        ));
    }

    let wire = wires[col as usize];
    Ok(External::new(wire))
}

fn purescript_gate_kind_to_rust_gate_type(gate_kind: &str) -> Result<GateType> {
    match gate_kind {
        "Zero" => Ok(GateType::Zero),
        "GenericPlonkGate" => Ok(GateType::Generic),
        "PoseidonGate" => Ok(GateType::Poseidon),
        "AddCompleteGate" => Ok(GateType::CompleteAdd),
        "VarBaseMul" => Ok(GateType::VarBaseMul),
        "EndoMul" => Ok(GateType::EndoMul),
        "EndoScalar" => Ok(GateType::EndoMulScalar),
        _ => Err(Error::new(
            Status::InvalidArg,
            format!("Invalid PureScript gate kind: '{gate_kind}'. Valid kinds: Zero, GenericPlonkGate, PoseidonGate, AddCompleteGate, VarBaseMul, EndoMul, EndoScalar"),
        )),
    }
}

#[napi]
pub fn pallas_circuit_gate_new(
    gate_kind: String,
    wires: &GateWiresExternal,
    coeffs: Vec<&PallasFieldExternal>,
) -> Result<PallasCircuitGateExternal> {
    let coeffs_vec: Vec<PallasScalarField> = coeffs.iter().map(|c| ***c).collect();
    let circuit_gate = generic::circuit_gate_new(&gate_kind, wires, coeffs_vec)?;
    Ok(External::new(circuit_gate))
}

#[napi]
pub fn pallas_circuit_gate_get_wires(gate: &PallasCircuitGateExternal) -> GateWiresExternal {
    External::new(gate.wires)
}

#[napi]
pub fn pallas_circuit_gate_coeff_count(gate: &PallasCircuitGateExternal) -> u32 {
    gate.coeffs.len() as u32
}

#[napi]
pub fn pallas_circuit_gate_get_coeff(
    gate: &PallasCircuitGateExternal,
    index: u32,
) -> Result<PallasFieldExternal> {
    let coeff = gate.coeffs.get(index as usize).ok_or_else(|| {
        Error::new(
            Status::InvalidArg,
            format!("Coefficient index {index} out of bounds"),
        )
    })?;
    Ok(External::new(*coeff))
}

#[napi]
pub fn vesta_circuit_gate_new(
    gate_kind: String,
    wires: &GateWiresExternal,
    coeffs: Vec<&VestaFieldExternal>,
) -> Result<VestaCircuitGateExternal> {
    let coeffs_vec: Vec<VestaScalarField> = coeffs.iter().map(|c| ***c).collect();
    let circuit_gate = generic::circuit_gate_new(&gate_kind, wires, coeffs_vec)?;
    Ok(External::new(circuit_gate))
}

#[napi]
pub fn vesta_circuit_gate_get_wires(gate: &VestaCircuitGateExternal) -> GateWiresExternal {
    External::new(gate.wires)
}

#[napi]
pub fn vesta_circuit_gate_coeff_count(gate: &VestaCircuitGateExternal) -> u32 {
    gate.coeffs.len() as u32
}

#[napi]
pub fn vesta_circuit_gate_get_coeff(
    gate: &VestaCircuitGateExternal,
    index: u32,
) -> Result<VestaFieldExternal> {
    let coeff = gate.coeffs.get(index as usize).ok_or_else(|| {
        Error::new(
            Status::InvalidArg,
            format!("Coefficient index {index} out of bounds"),
        )
    })?;
    Ok(External::new(*coeff))
}

#[napi]
pub fn pallas_constraint_system_create(
    gates: Vec<&PallasCircuitGateExternal>,
    public_inputs_count: u32,
) -> Result<PallasConstraintSystemExternal> {
    let internal_gates: Vec<CircuitGate<PallasScalarField>> = gates
        .into_iter()
        .map(|gate_ext| (**gate_ext).clone())
        .collect();

    let cs = generic::constraint_system_create(internal_gates, public_inputs_count as usize)?;
    Ok(External::new(cs))
}

#[napi]
pub fn vesta_constraint_system_create(
    gates: Vec<&VestaCircuitGateExternal>,
    public_inputs_count: u32,
) -> Result<VestaConstraintSystemExternal> {
    let internal_gates: Vec<CircuitGate<VestaScalarField>> = gates
        .into_iter()
        .map(|gate_ext| (**gate_ext).clone())
        .collect();

    let cs = generic::constraint_system_create(internal_gates, public_inputs_count as usize)?;
    Ok(External::new(cs))
}

fn load_srs_from_cache<G>(cache_path: &str) -> Result<SRS<G>>
where
    G: Clone,
    SRS<G>: serde::de::DeserializeOwned,
    TestSRS<G>: serde::de::DeserializeOwned + Into<SRS<G>>,
{
    let file_path = Path::new(cache_path);
    let file = File::open(file_path).map_err(|e| {
        Error::new(
            Status::GenericFailure,
            format!(
                "Error opening SRS cache file {}: {}",
                file_path.display(),
                e
            ),
        )
    })?;

    let srs = if file_path
        .file_name()
        .unwrap()
        .to_str()
        .unwrap()
        .starts_with("test_")
    {
        let test_srs: TestSRS<G> = rmp_serde::from_read(&file).map_err(|e| {
            Error::new(
                Status::GenericFailure,
                format!("Error deserializing test SRS: {e}"),
            )
        })?;
        test_srs.into()
    } else {
        rmp_serde::from_read(&file).map_err(|e| {
            Error::new(
                Status::GenericFailure,
                format!("Error deserializing SRS: {e}"),
            )
        })?
    };

    Ok(srs)
}

#[napi]
pub fn pallas_crs_load_from_cache() -> Result<PallasCRSExternal> {
    Ok(External::new(load_srs_from_cache("srs-cache/pallas.srs")?))
}

#[napi]
pub fn vesta_crs_load_from_cache() -> Result<VestaCRSExternal> {
    Ok(External::new(load_srs_from_cache("srs-cache/vesta.srs")?))
}

#[napi]
pub fn pallas_prover_index_create(
    cs: &PallasConstraintSystemExternal,
    endo_q: &PallasFieldExternal,
    srs: &PallasCRSExternal,
) -> PallasProverIndexExternal {
    let prover_index = ProverIndex::create(
        (**cs).clone(),
        **endo_q,
        Arc::new((**srs).clone()),
        false, // lazy_mode
    );
    External::new(prover_index)
}

#[napi]
pub fn vesta_prover_index_create(
    cs: &VestaConstraintSystemExternal,
    endo_q: &VestaFieldExternal,
    srs: &VestaCRSExternal,
) -> VestaProverIndexExternal {
    let prover_index = ProverIndex::create(
        (**cs).clone(),
        **endo_q,
        Arc::new((**srs).clone()),
        false, // lazy_mode
    );
    External::new(prover_index)
}

#[napi]
pub fn pallas_prover_index_verify(
    prover_index: &PallasProverIndexExternal,
    witness_columns: Vec<Vec<&External<PallasScalarField>>>,
    public_inputs: Vec<&PallasFieldExternal>,
) -> bool {
    let witness: [Vec<PallasScalarField>; COLUMNS] = std::array::from_fn(|i| {
        witness_columns[i]
            .iter()
            .map(|field_ext| ***field_ext)
            .collect()
    });
    let public: Vec<PallasScalarField> = public_inputs.iter().map(|f| ***f).collect();
    generic::prover_index_verify(&**prover_index, &witness, &public)
}

#[napi]
pub fn vesta_prover_index_verify(
    prover_index: &VestaProverIndexExternal,
    witness_columns: Vec<Vec<&External<VestaScalarField>>>,
    public_inputs: Vec<&VestaFieldExternal>,
) -> bool {
    let witness: [Vec<VestaScalarField>; COLUMNS] = std::array::from_fn(|i| {
        witness_columns[i]
            .iter()
            .map(|field_ext| ***field_ext)
            .collect()
    });
    let public: Vec<VestaScalarField> = public_inputs.iter().map(|f| ***f).collect();
    generic::prover_index_verify(&**prover_index, &witness, &public)
}

/// Get the domain log2 size from a Vesta prover index (for Pallas linearization).
#[napi]
pub fn pallas_prover_index_domain_log2(prover_index: &VestaProverIndexExternal) -> u32 {
    prover_index.cs.domain.d1.log_size_of_group() as u32
}

/// Get the domain log2 size from a Pallas prover index (for Vesta linearization).
#[napi]
pub fn vesta_prover_index_domain_log2(prover_index: &PallasProverIndexExternal) -> u32 {
    prover_index.cs.domain.d1.log_size_of_group() as u32
}

/// Compute witness polynomial evaluations from a Vesta prover index.
/// Returns 30 values: 15 columns × 2 points (zeta, zeta*omega).
#[napi]
pub fn pallas_prover_index_witness_evaluations(
    prover_index: &VestaProverIndexExternal,
    witness_columns: Vec<Vec<&VestaFieldExternal>>,
    zeta: &VestaFieldExternal,
) -> Result<Vec<VestaFieldExternal>> {
    let cols: Vec<Vec<VestaScalarField>> = witness_columns
        .iter()
        .map(|col| col.iter().map(|x| ***x).collect())
        .collect();
    let result = generic::witness_evaluations(prover_index.cs.domain.d1, cols, **zeta);
    Ok(result.into_iter().map(External::new).collect())
}

/// Compute coefficient polynomial evaluations from a Vesta prover index.
/// Returns 15 coefficient evaluations at zeta.
#[napi]
pub fn pallas_prover_index_coefficient_evaluations(
    prover_index: &VestaProverIndexExternal,
    zeta: &VestaFieldExternal,
) -> Result<Vec<VestaFieldExternal>> {
    let result =
        generic::coefficient_evaluations(prover_index.cs.domain.d1, &prover_index.cs.gates, **zeta);
    Ok(result.into_iter().map(External::new).collect())
}

/// Compute selector polynomial evaluations from a Vesta prover index.
/// Returns 12 values: 6 gate types × 2 points (zeta, zeta*omega).
#[napi]
pub fn pallas_prover_index_selector_evaluations(
    prover_index: &VestaProverIndexExternal,
    zeta: &VestaFieldExternal,
) -> Result<Vec<VestaFieldExternal>> {
    let result =
        generic::selector_evaluations(prover_index.cs.domain.d1, &prover_index.cs.gates, **zeta);
    Ok(result.into_iter().map(External::new).collect())
}

/// Compute witness polynomial evaluations from a Pallas prover index (for Vesta linearization).
/// Returns 30 values: 15 columns × 2 points (zeta, zeta*omega).
#[napi]
pub fn vesta_prover_index_witness_evaluations(
    prover_index: &PallasProverIndexExternal,
    witness_columns: Vec<Vec<&PallasFieldExternal>>,
    zeta: &PallasFieldExternal,
) -> Result<Vec<PallasFieldExternal>> {
    let cols: Vec<Vec<PallasScalarField>> = witness_columns
        .iter()
        .map(|col| col.iter().map(|x| ***x).collect())
        .collect();
    let result = generic::witness_evaluations(prover_index.cs.domain.d1, cols, **zeta);
    Ok(result.into_iter().map(External::new).collect())
}

/// Compute coefficient polynomial evaluations from a Pallas prover index.
#[napi]
pub fn vesta_prover_index_coefficient_evaluations(
    prover_index: &PallasProverIndexExternal,
    zeta: &PallasFieldExternal,
) -> Result<Vec<PallasFieldExternal>> {
    let result =
        generic::coefficient_evaluations(prover_index.cs.domain.d1, &prover_index.cs.gates, **zeta);
    Ok(result.into_iter().map(External::new).collect())
}

/// Compute selector polynomial evaluations from a Pallas prover index.
#[napi]
pub fn vesta_prover_index_selector_evaluations(
    prover_index: &PallasProverIndexExternal,
    zeta: &PallasFieldExternal,
) -> Result<Vec<PallasFieldExternal>> {
    let result =
        generic::selector_evaluations(prover_index.cs.domain.d1, &prover_index.cs.gates, **zeta);
    Ok(result.into_iter().map(External::new).collect())
}

// ─── Proof creation and oracle computation ───────────────────────────────────

/// Get the 7 shift values from a Vesta prover index (for Pallas linearization).
#[napi]
pub fn pallas_prover_index_shifts(
    prover_index: &VestaProverIndexExternal,
) -> Vec<VestaFieldExternal> {
    generic::prover_index_shifts(&**prover_index)
        .into_iter()
        .map(External::new)
        .collect()
}

/// Get the 7 shift values from a Pallas prover index (for Vesta linearization).
#[napi]
pub fn vesta_prover_index_shifts(
    prover_index: &PallasProverIndexExternal,
) -> Vec<PallasFieldExternal> {
    generic::prover_index_shifts(&**prover_index)
        .into_iter()
        .map(External::new)
        .collect()
}

/// Create a proof using a Vesta prover index (Pallas/Fp circuits).
#[napi]
pub fn pallas_create_proof(
    prover_index: &VestaProverIndexExternal,
    witness_columns: Vec<Vec<&VestaFieldExternal>>,
) -> Result<VestaProofExternal> {
    let witness: [Vec<VestaScalarField>; COLUMNS] = std::array::from_fn(|i| {
        witness_columns[i]
            .iter()
            .map(|field_ext| ***field_ext)
            .collect()
    });
    let proof = generic::create_proof::<VestaGroup, VestaBaseSponge, VestaScalarSponge>(
        &**prover_index,
        witness,
    )?;
    Ok(External::new(proof))
}

/// Create a proof using a Pallas prover index (Vesta/Fq circuits).
#[napi]
pub fn vesta_create_proof(
    prover_index: &PallasProverIndexExternal,
    witness_columns: Vec<Vec<&PallasFieldExternal>>,
) -> Result<PallasProofExternal> {
    let witness: [Vec<PallasScalarField>; COLUMNS] = std::array::from_fn(|i| {
        witness_columns[i]
            .iter()
            .map(|field_ext| ***field_ext)
            .collect()
    });
    let proof = generic::create_proof::<PallasGroup, PallasBaseSponge, PallasScalarSponge>(
        &**prover_index,
        witness,
    )?;
    Ok(External::new(proof))
}

/// Extract witness evaluations from a Vesta proof (Pallas/Fp circuits).
/// Returns 30 values: 15 columns x 2 points (zeta, zeta*omega).
#[napi]
pub fn pallas_proof_witness_evals(proof: &VestaProofExternal) -> Vec<VestaFieldExternal> {
    generic::proof_witness_evals(&**proof)
        .into_iter()
        .map(External::new)
        .collect()
}

/// Extract witness evaluations from a Pallas proof (Vesta/Fq circuits).
/// Returns 30 values: 15 columns x 2 points (zeta, zeta*omega).
#[napi]
pub fn vesta_proof_witness_evals(proof: &PallasProofExternal) -> Vec<PallasFieldExternal> {
    generic::proof_witness_evals(&**proof)
        .into_iter()
        .map(External::new)
        .collect()
}

/// Extract z (permutation polynomial) evaluations from a Vesta proof.
/// Returns 2 values: z(zeta), z(zeta*omega).
#[napi]
pub fn pallas_proof_z_evals(proof: &VestaProofExternal) -> Vec<VestaFieldExternal> {
    generic::proof_z_evals(&**proof)
        .into_iter()
        .map(External::new)
        .collect()
}

/// Extract z (permutation polynomial) evaluations from a Pallas proof.
/// Returns 2 values: z(zeta), z(zeta*omega).
#[napi]
pub fn vesta_proof_z_evals(proof: &PallasProofExternal) -> Vec<PallasFieldExternal> {
    generic::proof_z_evals(&**proof)
        .into_iter()
        .map(External::new)
        .collect()
}

/// Extract sigma evaluations from a Vesta proof (Pallas/Fp circuits).
/// Returns 12 values: 6 sigma columns x 2 points (zeta, zeta*omega).
#[napi]
pub fn pallas_proof_sigma_evals(proof: &VestaProofExternal) -> Vec<VestaFieldExternal> {
    generic::proof_sigma_evals(&**proof)
        .into_iter()
        .map(External::new)
        .collect()
}

/// Extract sigma evaluations from a Pallas proof (Vesta/Fq circuits).
/// Returns 12 values: 6 sigma columns x 2 points (zeta, zeta*omega).
#[napi]
pub fn vesta_proof_sigma_evals(proof: &PallasProofExternal) -> Vec<PallasFieldExternal> {
    generic::proof_sigma_evals(&**proof)
        .into_iter()
        .map(External::new)
        .collect()
}

/// Extract coefficient evaluations from a Vesta proof (Pallas/Fp circuits).
/// Returns 30 values: 15 coefficient columns x 2 points (zeta, zeta*omega).
#[napi]
pub fn pallas_proof_coefficient_evals(proof: &VestaProofExternal) -> Vec<VestaFieldExternal> {
    generic::proof_coefficient_evals(&**proof)
        .into_iter()
        .map(External::new)
        .collect()
}

/// Extract coefficient evaluations from a Pallas proof (Vesta/Fq circuits).
/// Returns 30 values: 15 coefficient columns x 2 points (zeta, zeta*omega).
#[napi]
pub fn vesta_proof_coefficient_evals(proof: &PallasProofExternal) -> Vec<PallasFieldExternal> {
    generic::proof_coefficient_evals(&**proof)
        .into_iter()
        .map(External::new)
        .collect()
}

/// Run Fiat-Shamir oracle computation on a Vesta proof (Pallas/Fp circuits).
/// Returns 11 values: [alpha, beta, gamma, zeta, ft_eval0, v, u,
///                     combined_inner_product, ft_eval1, public_eval_zeta, public_eval_zeta_omega]
#[napi]
pub fn pallas_proof_oracles(
    prover_index: &VestaProverIndexExternal,
    proof: &VestaProofExternal,
    public_input: Vec<&VestaFieldExternal>,
) -> Result<Vec<VestaFieldExternal>> {
    let public: Vec<VestaScalarField> = public_input.iter().map(|f| ***f).collect();
    let result = generic::proof_oracles::<VestaGroup, VestaBaseSponge, VestaScalarSponge>(
        &**prover_index,
        &**proof,
        &public,
    )?;
    Ok(result.into_iter().map(External::new).collect())
}

/// Run Fiat-Shamir oracle computation on a Pallas proof (Vesta/Fq circuits).
/// Returns 11 values: [alpha, beta, gamma, zeta, ft_eval0, v, u,
///                     combined_inner_product, ft_eval1, public_eval_zeta, public_eval_zeta_omega]
#[napi]
pub fn vesta_proof_oracles(
    prover_index: &PallasProverIndexExternal,
    proof: &PallasProofExternal,
    public_input: Vec<&PallasFieldExternal>,
) -> Result<Vec<PallasFieldExternal>> {
    let public: Vec<PallasScalarField> = public_input.iter().map(|f| ***f).collect();
    let result = generic::proof_oracles::<PallasGroup, PallasBaseSponge, PallasScalarSponge>(
        &**prover_index,
        &**proof,
        &public,
    )?;
    Ok(result.into_iter().map(External::new).collect())
}

/// Extract sponge-derived verifier data from a Vesta proof (Pallas/Fp circuits).
/// Returns flat array: [challenges..., u_x, u_y, c]
/// - challenges (d values): in ScalarField (Fp)
/// - u_x, u_y: U point coords in BaseField (Fq)
/// - c: final challenge in ScalarField (Fp), 128-bit truncated
#[napi]
pub fn pallas_proof_bulletproof_challenges(
    prover_index: &VestaProverIndexExternal,
    proof: &VestaProofExternal,
    public_input: Vec<&VestaFieldExternal>,
) -> Result<Vec<VestaFieldExternal>> {
    let public: Vec<VestaScalarField> = public_input.iter().map(|f| ***f).collect();
    let (challenges, _u_x, _u_y, c) = generic::proof_bulletproof_challenges::<
        VestaGroup,
        VestaBaseSponge,
        VestaScalarSponge,
    >(&**prover_index, &**proof, &public)?;
    // Return challenges and c (both in ScalarField)
    // u_x, u_y are in BaseField - return separately via pallas_proof_u_point
    let mut result: Vec<VestaFieldExternal> = challenges.into_iter().map(External::new).collect();
    result.push(External::new(c));
    Ok(result)
}

/// Extract U point from a Vesta proof (Pallas/Fp circuits).
/// Returns [u_x, u_y] in BaseField (Fq = Pallas.ScalarField).
#[napi]
pub fn pallas_proof_u_point(
    prover_index: &VestaProverIndexExternal,
    proof: &VestaProofExternal,
    public_input: Vec<&VestaFieldExternal>,
) -> Result<Vec<PallasFieldExternal>> {
    let public: Vec<VestaScalarField> = public_input.iter().map(|f| ***f).collect();
    let (_, u_x, u_y, _) = generic::proof_bulletproof_challenges::<
        VestaGroup,
        VestaBaseSponge,
        VestaScalarSponge,
    >(&**prover_index, &**proof, &public)?;
    Ok(vec![External::new(u_x), External::new(u_y)])
}

/// Extract sponge-derived verifier data from a Pallas proof (Vesta/Fq circuits).
/// Returns flat array: [challenges..., c]
/// - challenges (d values): in ScalarField (Fq)
/// - c: final challenge in ScalarField (Fq), 128-bit truncated
#[napi]
pub fn vesta_proof_bulletproof_challenges(
    prover_index: &PallasProverIndexExternal,
    proof: &PallasProofExternal,
    public_input: Vec<&PallasFieldExternal>,
) -> Result<Vec<PallasFieldExternal>> {
    let public: Vec<PallasScalarField> = public_input.iter().map(|f| ***f).collect();
    let (challenges, _u_x, _u_y, c) = generic::proof_bulletproof_challenges::<
        PallasGroup,
        PallasBaseSponge,
        PallasScalarSponge,
    >(&**prover_index, &**proof, &public)?;
    let mut result: Vec<PallasFieldExternal> = challenges.into_iter().map(External::new).collect();
    result.push(External::new(c));
    Ok(result)
}

/// Extract U point from a Pallas proof (Vesta/Fq circuits).
/// Returns [u_x, u_y] in BaseField (Fp = Vesta.ScalarField).
#[napi]
pub fn vesta_proof_u_point(
    prover_index: &PallasProverIndexExternal,
    proof: &PallasProofExternal,
    public_input: Vec<&PallasFieldExternal>,
) -> Result<Vec<VestaFieldExternal>> {
    let public: Vec<PallasScalarField> = public_input.iter().map(|f| ***f).collect();
    let (_, u_x, u_y, _) = generic::proof_bulletproof_challenges::<
        PallasGroup,
        PallasBaseSponge,
        PallasScalarSponge,
    >(&**prover_index, &**proof, &public)?;
    Ok(vec![External::new(u_x), External::new(u_y)])
}

/// Verify opening proof for a Vesta proof (Pallas/Fp circuits).
/// Returns true if verification succeeds.
#[napi]
pub fn pallas_verify_opening_proof(
    prover_index: &VestaProverIndexExternal,
    proof: &VestaProofExternal,
    public_input: Vec<&VestaFieldExternal>,
) -> bool {
    let public: Vec<VestaScalarField> = public_input.iter().map(|f| ***f).collect();
    generic::verify_opening_proof::<VestaGroup, VestaBaseSponge, VestaScalarSponge>(
        &**prover_index,
        &**proof,
        &public,
    )
}

/// Verify opening proof for a Pallas proof (Vesta/Fq circuits).
/// Returns true if verification succeeds.
#[napi]
pub fn vesta_verify_opening_proof(
    prover_index: &PallasProverIndexExternal,
    proof: &PallasProofExternal,
    public_input: Vec<&PallasFieldExternal>,
) -> bool {
    let public: Vec<PallasScalarField> = public_input.iter().map(|f| ***f).collect();
    generic::verify_opening_proof::<PallasGroup, PallasBaseSponge, PallasScalarSponge>(
        &**prover_index,
        &**proof,
        &public,
    )
}

/// Compute b0 for a Vesta proof (Pallas/Fp circuits).
/// b0 = b_poly(challenges, zeta) + evalscale * b_poly(challenges, zeta_omega)
#[napi]
pub fn pallas_compute_b0(
    challenges: Vec<&VestaFieldExternal>,
    zeta: &VestaFieldExternal,
    zeta_omega: &VestaFieldExternal,
    evalscale: &VestaFieldExternal,
) -> VestaFieldExternal {
    let chals: Vec<VestaScalarField> = challenges.iter().map(|c| ***c).collect();
    let result = generic::compute_b0(&chals, **zeta, **zeta_omega, **evalscale);
    External::new(result)
}

/// Compute b0 for a Pallas proof (Vesta/Fq circuits).
/// b0 = b_poly(challenges, zeta) + evalscale * b_poly(challenges, zeta_omega)
#[napi]
pub fn vesta_compute_b0(
    challenges: Vec<&PallasFieldExternal>,
    zeta: &PallasFieldExternal,
    zeta_omega: &PallasFieldExternal,
    evalscale: &PallasFieldExternal,
) -> PallasFieldExternal {
    let chals: Vec<PallasScalarField> = challenges.iter().map(|c| ***c).collect();
    let result = generic::compute_b0(&chals, **zeta, **zeta_omega, **evalscale);
    External::new(result)
}

/// Get the number of IPA rounds (domain log2) from a Vesta proof.
#[napi]
pub fn pallas_proof_ipa_rounds(proof: &VestaProofExternal) -> u32 {
    proof.proof.lr.len() as u32
}

/// Get the number of IPA rounds (domain log2) from a Pallas proof.
#[napi]
pub fn vesta_proof_ipa_rounds(proof: &PallasProofExternal) -> u32 {
    proof.proof.lr.len() as u32
}

/// Extract sg commitment coordinates from a Vesta proof (Pallas/Fp circuits).
/// Returns 2 values: [sg.x, sg.y] in PallasScalarField (= Vesta base field Fp).
/// These are needed for the deferred IPA verification check.
#[napi]
pub fn pallas_proof_sg(proof: &VestaProofExternal) -> Vec<PallasFieldExternal> {
    use ark_ec::AffineRepr;
    let sg = &proof.proof.sg;
    let x = sg.x().unwrap();
    let y = sg.y().unwrap();
    vec![External::new(x), External::new(y)]
}

/// Extract sg commitment coordinates from a Pallas proof (Vesta/Fq circuits).
/// Returns 2 values: [sg.x, sg.y] in VestaScalarField (= Pallas base field Fq).
/// These are needed for the deferred IPA verification check.
#[napi]
pub fn vesta_proof_sg(proof: &PallasProofExternal) -> Vec<VestaFieldExternal> {
    use ark_ec::AffineRepr;
    let sg = &proof.proof.sg;
    let x = sg.x().unwrap();
    let y = sg.y().unwrap();
    vec![External::new(x), External::new(y)]
}

/// Verify the deferred sg commitment check entirely in Rust (for debugging).
/// This duplicates the logic from proof_bulletproof_challenges + pallas_verify_deferred_check
/// to verify the full chain works correctly.
#[napi]
pub fn pallas_verify_deferred_check_internal(
    prover_index: &VestaProverIndexExternal,
    proof: &VestaProofExternal,
    public_input: Vec<&VestaFieldExternal>,
) -> Result<bool> {
    use ark_ec::{AffineRepr, CurveGroup, VariableBaseMSM};
    use mina_poseidon::FqSponge;
    use poly_commitment::commitment::b_poly_coefficients;

    let public: Vec<VestaScalarField> = public_input.iter().map(|f| ***f).collect();

    // Compute oracles (same as in proof_bulletproof_challenges)
    let (_, oracles_result) = generic::compute_oracles::<
        VestaGroup,
        VestaBaseSponge,
        VestaScalarSponge,
    >(&**prover_index, &**proof, &public)?;

    // Follow SRS::verify flow exactly
    let mut fq_sponge = oracles_result.fq_sponge;

    let shifted_cip = poly_commitment::commitment::shift_scalar::<VestaGroup>(
        oracles_result.combined_inner_product,
    );
    fq_sponge.absorb_fr(&[shifted_cip]);

    // Squeeze challenge_fq for u_base (advances sponge state)
    let _u_base_t = fq_sponge.challenge_fq();

    // Get challenges using the CANONICAL endomorphism coefficient to match SRS::verify behavior
    let canonical_endo_r = vesta_endos().1;
    let challenges = proof.proof.challenges(&canonical_endo_r, &mut fq_sponge);
    let chal = &challenges.chal;

    // Compute b_poly_coefficients
    let s = b_poly_coefficients(chal);

    // Get sg from proof
    let sg = proof.proof.sg;

    // Compute MSM using the SRS from prover_index
    let g = &prover_index.srs.g;

    if g.len() < s.len() {
        return Ok(false);
    }

    let bases: Vec<VestaGroup> = g.iter().take(s.len()).cloned().collect();
    let computed = <VestaGroup as AffineRepr>::Group::msm_unchecked(&bases, &s).into_affine();

    Ok(computed == sg)
}

// ─── Opening Proof Data Extraction ───────────────────────────────────────────

/// Extract L/R pairs from a proof's opening proof.
/// Returns 4*d values: d pairs of (L.x, L.y, R.x, R.y) coordinates.
/// Coordinates are in the curve's base field.
#[napi]
pub fn pallas_proof_opening_lr(proof: &VestaProofExternal) -> Vec<PallasFieldExternal> {
    use ark_ec::AffineRepr;
    let mut result = Vec::with_capacity(proof.proof.lr.len() * 4);
    for (l, r) in &proof.proof.lr {
        result.push(External::new(l.x().unwrap()));
        result.push(External::new(l.y().unwrap()));
        result.push(External::new(r.x().unwrap()));
        result.push(External::new(r.y().unwrap()));
    }
    result
}

/// Extract L/R pairs from a Pallas proof's opening proof.
#[napi]
pub fn vesta_proof_opening_lr(proof: &PallasProofExternal) -> Vec<VestaFieldExternal> {
    use ark_ec::AffineRepr;
    let mut result = Vec::with_capacity(proof.proof.lr.len() * 4);
    for (l, r) in &proof.proof.lr {
        result.push(External::new(l.x().unwrap()));
        result.push(External::new(l.y().unwrap()));
        result.push(External::new(r.x().unwrap()));
        result.push(External::new(r.y().unwrap()));
    }
    result
}

/// Extract delta commitment from a Vesta proof's opening proof.
/// Returns 2 values: [delta.x, delta.y] in PallasScalarField.
#[napi]
pub fn pallas_proof_opening_delta(proof: &VestaProofExternal) -> Vec<PallasFieldExternal> {
    use ark_ec::AffineRepr;
    let delta = &proof.proof.delta;
    vec![
        External::new(delta.x().unwrap()),
        External::new(delta.y().unwrap()),
    ]
}

/// Extract delta commitment from a Pallas proof's opening proof.
/// Returns 2 values: [delta.x, delta.y] in VestaScalarField.
#[napi]
pub fn vesta_proof_opening_delta(proof: &PallasProofExternal) -> Vec<VestaFieldExternal> {
    use ark_ec::AffineRepr;
    let delta = &proof.proof.delta;
    vec![
        External::new(delta.x().unwrap()),
        External::new(delta.y().unwrap()),
    ]
}

/// Extract z1 scalar from a Vesta proof's opening proof.
#[napi]
pub fn pallas_proof_opening_z1(proof: &VestaProofExternal) -> VestaFieldExternal {
    External::new(proof.proof.z1)
}

/// Extract z1 scalar from a Pallas proof's opening proof.
#[napi]
pub fn vesta_proof_opening_z1(proof: &PallasProofExternal) -> PallasFieldExternal {
    External::new(proof.proof.z1)
}

/// Extract z2 scalar from a Vesta proof's opening proof.
#[napi]
pub fn pallas_proof_opening_z2(proof: &VestaProofExternal) -> VestaFieldExternal {
    External::new(proof.proof.z2)
}

/// Extract z2 scalar from a Pallas proof's opening proof.
#[napi]
pub fn vesta_proof_opening_z2(proof: &PallasProofExternal) -> PallasFieldExternal {
    External::new(proof.proof.z2)
}

/// Extract H generator from a Vesta prover index's SRS.
/// Returns 2 values: [h.x, h.y] in PallasScalarField (= Vesta base field).
#[napi]
pub fn pallas_prover_index_h(prover_index: &VestaProverIndexExternal) -> Vec<PallasFieldExternal> {
    use ark_ec::AffineRepr;
    let h = &prover_index.srs.h;
    vec![
        External::new(h.x().unwrap()),
        External::new(h.y().unwrap()),
    ]
}

/// Extract H generator from a Pallas prover index's SRS.
/// Returns 2 values: [h.x, h.y] in VestaScalarField (= Pallas base field).
#[napi]
pub fn vesta_prover_index_h(prover_index: &PallasProverIndexExternal) -> Vec<VestaFieldExternal> {
    use ark_ec::AffineRepr;
    let h = &prover_index.srs.h;
    vec![
        External::new(h.x().unwrap()),
        External::new(h.y().unwrap()),
    ]
}

// ─── Proof Commitments Extraction ────────────────────────────────────────────

/// Extract witness polynomial commitments from a Vesta proof.
/// Returns 30 values: 15 commitments × 2 coordinates (x, y).
/// Each commitment is the first (non-chunked) point from w_comm[i].
#[napi]
pub fn pallas_proof_w_comm(proof: &VestaProofExternal) -> Vec<PallasFieldExternal> {
    use ark_ec::AffineRepr;
    let mut result = Vec::with_capacity(COLUMNS * 2);
    for w in &proof.commitments.w_comm {
        // Take the first (and typically only) point from each PolyComm
        if let Some(pt) = w.chunks.first() {
            result.push(External::new(pt.x().unwrap()));
            result.push(External::new(pt.y().unwrap()));
        }
    }
    result
}

/// Extract witness polynomial commitments from a Pallas proof.
#[napi]
pub fn vesta_proof_w_comm(proof: &PallasProofExternal) -> Vec<VestaFieldExternal> {
    use ark_ec::AffineRepr;
    let mut result = Vec::with_capacity(COLUMNS * 2);
    for w in &proof.commitments.w_comm {
        if let Some(pt) = w.chunks.first() {
            result.push(External::new(pt.x().unwrap()));
            result.push(External::new(pt.y().unwrap()));
        }
    }
    result
}

/// Extract z (permutation) polynomial commitment from a Vesta proof.
/// Returns 2 values: [z.x, z.y].
#[napi]
pub fn pallas_proof_z_comm(proof: &VestaProofExternal) -> Vec<PallasFieldExternal> {
    use ark_ec::AffineRepr;
    let z = proof.commitments.z_comm.chunks.first().unwrap();
    vec![External::new(z.x().unwrap()), External::new(z.y().unwrap())]
}

/// Extract z (permutation) polynomial commitment from a Pallas proof.
#[napi]
pub fn vesta_proof_z_comm(proof: &PallasProofExternal) -> Vec<VestaFieldExternal> {
    use ark_ec::AffineRepr;
    let z = proof.commitments.z_comm.chunks.first().unwrap();
    vec![External::new(z.x().unwrap()), External::new(z.y().unwrap())]
}

/// Extract t (quotient) polynomial commitment from a Vesta proof.
/// Returns 2*chunks values: chunks × 2 coordinates (x, y).
/// The t polynomial may be chunked for large circuits.
#[napi]
pub fn pallas_proof_t_comm(proof: &VestaProofExternal) -> Vec<PallasFieldExternal> {
    use ark_ec::AffineRepr;
    let mut result = Vec::with_capacity(proof.commitments.t_comm.chunks.len() * 2);
    for pt in &proof.commitments.t_comm.chunks {
        result.push(External::new(pt.x().unwrap()));
        result.push(External::new(pt.y().unwrap()));
    }
    result
}

/// Extract t (quotient) polynomial commitment from a Pallas proof.
#[napi]
pub fn vesta_proof_t_comm(proof: &PallasProofExternal) -> Vec<VestaFieldExternal> {
    use ark_ec::AffineRepr;
    let mut result = Vec::with_capacity(proof.commitments.t_comm.chunks.len() * 2);
    for pt in &proof.commitments.t_comm.chunks {
        result.push(External::new(pt.x().unwrap()));
        result.push(External::new(pt.y().unwrap()));
    }
    result
}
