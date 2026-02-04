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
mod generic {
    use super::*;
    use ark_ec::{CurveGroup, VariableBaseMSM};
    use ark_ff::Field;
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
    fn compute_oracles<G, EFqSponge, EFrSponge>(
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
    /// Returns 12 values: [alpha, beta, gamma, zeta, ft_eval0, v, u,
    ///                     combined_inner_product, ft_eval1, public_eval_zeta, public_eval_zeta_omega,
    ///                     fq_digest]
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
            oracles_result.digest, // fq_digest: Fq-sponge state before Fr-sponge
        ])
    }

    /// Result of bulletproof challenge computation, including intermediate state.
    pub struct BulletproofChallengeData<F, Fq> {
        /// The endo-mapped challenges (what verification uses)
        pub challenges: Vec<F>,
        /// Sponge checkpoint just before L/R processing (from proof-systems)
        pub sponge_checkpoint: mina_poseidon::sponge::SpongeCheckpoint<Fq>,
    }

    /// Core helper: compute bulletproof challenges and extract all intermediate state.
    /// This is the single source of truth - other functions project from this.
    pub fn bulletproof_challenge_data<G, EFqSponge, EFrSponge>(
        prover_index: &ProverIndex<G, OpeningProof<G>>,
        proof: &ProverProof<G, OpeningProof<G>>,
        public_input: &[G::ScalarField],
    ) -> Result<BulletproofChallengeData<G::ScalarField, G::BaseField>>
    where
        G: KimchiCurve,
        G::BaseField: PrimeField,
        EFqSponge: Clone + mina_poseidon::FqSponge<G::BaseField, G, G::ScalarField>,
        EFrSponge: kimchi::plonk_sponge::FrSponge<G::ScalarField>,
        kimchi::verifier_index::VerifierIndex<G, OpeningProof<G>>: Clone,
    {
        let (verifier_index, oracles_result) =
            compute_oracles::<G, EFqSponge, EFrSponge>(prover_index, proof, public_input)?;

        // Get the sponge from oracles, absorb combined_inner_product
        let mut fq_sponge = oracles_result.fq_sponge;
        fq_sponge.absorb_fr(&[poly_commitment::commitment::shift_scalar::<G>(
            oracles_result.combined_inner_product,
        )]);

        // Capture sponge checkpoint BEFORE challenge extraction using trait method
        // This is after absorbing CIP but before squeezing for u
        let sponge_checkpoint = fq_sponge.checkpoint();

        // Squeeze for u (matches ipa.rs verifier which does this before calling challenges())
        // The u value itself is derived via group_map in the circuit, but we need to
        // advance the sponge state here to match the verifier's Fiat-Shamir transcript.
        let _u = fq_sponge.challenge_fq();

        // Get the challenges using the endomorphism coefficient
        let challenges = proof.proof.challenges(&verifier_index.endo, &mut fq_sponge);

        Ok(BulletproofChallengeData {
            challenges: challenges.chal,
            sponge_checkpoint,
        })
    }

    /// Extract bulletproof challenges from a proof.
    /// These are the IPA challenges after applying the endomorphism.
    /// Returns d values where d = domain_log2 (number of IPA rounds).
    pub fn proof_bulletproof_challenges<G, EFqSponge, EFrSponge>(
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
        Ok(bulletproof_challenge_data::<G, EFqSponge, EFrSponge>(
            prover_index,
            proof,
            public_input,
        )?
        .challenges)
    }

    /// Extract opening proof L/R pairs as flat coordinate array.
    /// Returns [L0.x, L0.y, R0.x, R0.y, L1.x, L1.y, R1.x, R1.y, ...]
    pub fn proof_opening_lr<G: KimchiCurve>(
        proof: &ProverProof<G, OpeningProof<G>>,
    ) -> Vec<G::BaseField>
    where
        G::BaseField: PrimeField,
    {
        // L and R are already affine points (G: AffineRepr)
        // Use CommitmentCurve::to_coordinates to extract x,y
        let mut result = Vec::with_capacity(proof.proof.lr.len() * 4);
        for (l, r) in &proof.proof.lr {
            if let Some((lx, ly)) = l.to_coordinates() {
                result.push(lx);
                result.push(ly);
            }
            if let Some((rx, ry)) = r.to_coordinates() {
                result.push(rx);
                result.push(ry);
            }
        }
        result
    }

    /// Compute lr_prod: the curve point sum from bullet_reduce.
    /// lr_prod = Σ_i [chal_inv[i] * L_i + chal[i] * R_i]
    ///
    /// This is the intermediate value computed during IPA verification
    /// (see wrap_verifier.ml bullet_reduce / step_verifier.ml bullet_reduce).
    /// Returns coordinates [x, y] of the result point.
    pub fn proof_lr_prod<G, EFqSponge, EFrSponge>(
        prover_index: &ProverIndex<G, OpeningProof<G>>,
        proof: &ProverProof<G, OpeningProof<G>>,
        public_input: &[G::ScalarField],
    ) -> Result<Vec<G::BaseField>>
    where
        G: KimchiCurve,
        G::BaseField: PrimeField,
        EFqSponge: Clone + mina_poseidon::FqSponge<G::BaseField, G, G::ScalarField>,
        EFrSponge: kimchi::plonk_sponge::FrSponge<G::ScalarField>,
        kimchi::verifier_index::VerifierIndex<G, OpeningProof<G>>: Clone,
    {
        let (verifier_index, oracles_result) =
            compute_oracles::<G, EFqSponge, EFrSponge>(prover_index, proof, public_input)?;

        // Get the sponge from oracles, absorb combined_inner_product
        let mut fq_sponge = oracles_result.fq_sponge;
        fq_sponge.absorb_fr(&[poly_commitment::commitment::shift_scalar::<G>(
            oracles_result.combined_inner_product,
        )]);

        // Squeeze for u (matches ipa.rs verifier which does this before calling challenges())
        let _u = fq_sponge.challenge_fq();

        // Get the challenges using the endomorphism coefficient
        // This returns Challenges { chal, chal_inv }
        let challenges = proof.proof.challenges(&verifier_index.endo, &mut fq_sponge);

        // Compute lr_prod = Σ_i [chal_inv[i] * L_i + chal[i] * R_i]
        let lr_pairs = &proof.proof.lr;
        let n = lr_pairs.len();

        // Build scalars and points for MSM
        let mut scalars = Vec::with_capacity(2 * n);
        let mut points = Vec::with_capacity(2 * n);

        for (i, (l, r)) in lr_pairs.iter().enumerate() {
            scalars.push(challenges.chal_inv[i]);
            scalars.push(challenges.chal[i]);
            points.push(*l);
            points.push(*r);
        }

        // Perform MSM: result = Σ scalars[i] * points[i]
        let result = G::Group::msm_unchecked(&points, &scalars).into_affine();

        // Return coordinates
        if let Some((x, y)) = result.to_coordinates() {
            Ok(vec![x, y])
        } else {
            Err(Error::new(
                Status::GenericFailure,
                "lr_prod result is point at infinity",
            ))
        }
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
            Ok(()) => true,
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

    /// Extract opening proof delta (curve point).
    /// Returns [x, y] coordinates.
    pub fn proof_opening_delta<G: KimchiCurve>(
        proof: &ProverProof<G, OpeningProof<G>>,
    ) -> Vec<G::BaseField>
    where
        G::BaseField: PrimeField,
    {
        if let Some((x, y)) = proof.proof.delta.to_coordinates() {
            vec![x, y]
        } else {
            // Point at infinity - return zeros
            vec![G::BaseField::zero(), G::BaseField::zero()]
        }
    }

    /// Extract opening proof sg (challenge polynomial commitment).
    /// Returns [x, y] coordinates.
    pub fn proof_opening_sg<G: KimchiCurve>(
        proof: &ProverProof<G, OpeningProof<G>>,
    ) -> Vec<G::BaseField>
    where
        G::BaseField: PrimeField,
    {
        if let Some((x, y)) = proof.proof.sg.to_coordinates() {
            vec![x, y]
        } else {
            // Point at infinity - return zeros
            vec![G::BaseField::zero(), G::BaseField::zero()]
        }
    }

    /// Extract opening proof z1 scalar.
    pub fn proof_opening_z1<G: KimchiCurve>(
        proof: &ProverProof<G, OpeningProof<G>>,
    ) -> G::ScalarField {
        proof.proof.z1
    }

    /// Extract opening proof z2 scalar.
    pub fn proof_opening_z2<G: KimchiCurve>(
        proof: &ProverProof<G, OpeningProof<G>>,
    ) -> G::ScalarField {
        proof.proof.z2
    }

    /// Get the blinding generator H from the SRS via prover index.
    /// Returns [x, y] coordinates.
    pub fn prover_index_blinding_generator<G: KimchiCurve>(
        prover_index: &ProverIndex<G, OpeningProof<G>>,
    ) -> Vec<G::BaseField>
    where
        G::BaseField: PrimeField,
        kimchi::verifier_index::VerifierIndex<G, OpeningProof<G>>: Clone,
    {
        let verifier_index = prover_index.verifier_index();
        let h = verifier_index.srs().blinding_commitment();
        if let Some((x, y)) = h.to_coordinates() {
            vec![x, y]
        } else {
            // Point at infinity - return zeros
            vec![G::BaseField::zero(), G::BaseField::zero()]
        }
    }

    /// Compute the combined polynomial commitment.
    /// This matches exactly what the Kimchi verifier computes and passes to IPA.
    /// The key is that the evaluations list includes ft_comm (the linearized commitment),
    /// NOT the raw t_comm.
    ///
    /// Uses Kimchi's to_batch function to get the evaluations list,
    /// then combines the commitments using combine_commitments.
    ///
    /// Returns [x, y] coordinates of the combined commitment.
    pub fn combined_polynomial_commitment<G, EFqSponge, EFrSponge>(
        prover_index: &ProverIndex<G, OpeningProof<G>>,
        proof: &ProverProof<G, OpeningProof<G>>,
        public_input: &[G::ScalarField],
    ) -> Result<Vec<G::BaseField>>
    where
        G: KimchiCurve,
        G::BaseField: PrimeField,
        EFqSponge: Clone + mina_poseidon::FqSponge<G::BaseField, G, G::ScalarField>,
        EFrSponge: kimchi::plonk_sponge::FrSponge<G::ScalarField>,
        kimchi::verifier_index::VerifierIndex<G, OpeningProof<G>>: Clone,
    {
        use poly_commitment::commitment::combine_commitments;

        let verifier_index = prover_index.verifier_index();

        // Use Kimchi's to_batch to get the evaluations list in correct order
        let batch = kimchi::verifier::to_batch::<G, EFqSponge, EFrSponge, OpeningProof<G>>(
            &verifier_index,
            proof,
            public_input,
        )
        .map_err(|e| Error::new(Status::GenericFailure, format!("to_batch failed: {e:?}")))?;

        // Use combine_commitments to compute the combined commitment
        let mut scalars: Vec<G::ScalarField> = Vec::new();
        let mut points: Vec<G> = Vec::new();

        combine_commitments(
            &batch.evaluations,
            &mut scalars,
            &mut points,
            batch.polyscale,
            G::ScalarField::one(), // rand_base = 1 (we're not batching multiple proofs)
        );

        // Compute MSM
        let scalars_bigint: Vec<_> = scalars.iter().map(|s| s.into_bigint()).collect();
        let result = G::Group::msm_bigint(&points, &scalars_bigint).into_affine();

        if let Some((x, y)) = result.to_coordinates() {
            Ok(vec![x, y])
        } else {
            Err(Error::new(
                Status::GenericFailure,
                "combined_polynomial_commitment result is point at infinity",
            ))
        }
    }

    /// Debug verification that prints all intermediate IPA values.
    pub fn debug_verify<G, EFqSponge, EFrSponge>(
        prover_index: &ProverIndex<G, OpeningProof<G>>,
        proof: &ProverProof<G, OpeningProof<G>>,
        public_input: &[G::ScalarField],
    ) where
        G: KimchiCurve,
        G::BaseField: PrimeField,
        EFqSponge: Clone + mina_poseidon::FqSponge<G::BaseField, G, G::ScalarField>,
        EFrSponge: kimchi::plonk_sponge::FrSponge<G::ScalarField>,
        kimchi::verifier_index::VerifierIndex<G, OpeningProof<G>>: Clone,
    {
        use poly_commitment::commitment::b_poly;

        let (verifier_index, oracles_result) =
            match compute_oracles::<G, EFqSponge, EFrSponge>(prover_index, proof, public_input) {
                Ok(r) => r,
                Err(e) => {
                    eprintln!("Failed to compute oracles: {e:?}");
                    return;
                }
            };

        let oracles = &oracles_result.oracles;

        eprintln!("=== IPA Debug Verification ===");
        eprintln!(
            "combined_inner_product: {:?}",
            oracles_result.combined_inner_product
        );
        eprintln!("polyscale (v): {:?}", oracles.v);
        eprintln!("evalscale (u oracle): {:?}", oracles.u);
        eprintln!("zeta: {:?}", oracles.zeta);

        // Get the sponge, absorb combined_inner_product
        let mut fq_sponge = oracles_result.fq_sponge.clone();
        fq_sponge.absorb_fr(&[poly_commitment::commitment::shift_scalar::<G>(
            oracles_result.combined_inner_product,
        )]);

        // Derive u point from group map
        let group_map = <G as CommitmentCurve>::Map::setup();
        let u_challenge = fq_sponge.challenge_fq();
        let (u_x, u_y) = group_map.to_group(u_challenge);
        let u_point: G = G::of_coordinates(u_x, u_y);

        eprintln!("u_challenge (for group map): {u_challenge:?}");
        if let Some((x, y)) = u_point.to_coordinates() {
            eprintln!("u point: ({x:?}, {y:?})");
        }

        // Get challenges
        let challenges = proof.proof.challenges(&verifier_index.endo, &mut fq_sponge);
        eprintln!(
            "IPA challenges (first 3): {:?}",
            &challenges.chal[..3.min(challenges.chal.len())]
        );

        // Absorb delta, get c
        fq_sponge.absorb_g(&[proof.proof.delta]);
        let c = mina_poseidon::sponge::ScalarChallenge(fq_sponge.challenge())
            .to_field(&verifier_index.endo);
        eprintln!("c (final challenge): {c:?}");

        // Compute b0
        let omega = verifier_index.domain.group_gen;
        let zeta_omega = oracles.zeta * omega;
        let b0 = b_poly(&challenges.chal, oracles.zeta)
            + oracles.u * b_poly(&challenges.chal, zeta_omega);
        eprintln!("b0: {b0:?}");

        // Compute lr_prod
        let lr_pairs = &proof.proof.lr;
        let mut lr_scalars = Vec::with_capacity(2 * lr_pairs.len());
        let mut lr_points = Vec::with_capacity(2 * lr_pairs.len());
        for (i, (l, r)) in lr_pairs.iter().enumerate() {
            lr_scalars.push(challenges.chal_inv[i]);
            lr_scalars.push(challenges.chal[i]);
            lr_points.push(*l);
            lr_points.push(*r);
        }
        let lr_prod = G::Group::msm_unchecked(&lr_points, &lr_scalars).into_affine();
        if let Some((x, y)) = lr_prod.to_coordinates() {
            eprintln!("lr_prod: ({x:?}, {y:?})");
        }

        // Print proof fields
        if let Some((x, y)) = proof.proof.delta.to_coordinates() {
            eprintln!("delta: ({x:?}, {y:?})");
        }
        if let Some((x, y)) = proof.proof.sg.to_coordinates() {
            eprintln!("sg: ({x:?}, {y:?})");
        }
        eprintln!("z1: {:?}", proof.proof.z1);
        eprintln!("z2: {:?}", proof.proof.z2);

        // Get H (blinding generator)
        let h = verifier_index.srs().blinding_commitment();
        if let Some((x, y)) = h.to_coordinates() {
            eprintln!("H (blinding generator): ({x:?}, {y:?})");
        }

        // Now let's compute the LHS and RHS of the IPA equation
        // LHS = c*Q + delta where Q = combined_comm + combined_inner_product*u + lr_prod
        // RHS = z1*(sg + b*u) + z2*H

        // For combined_comm, we need to combine all evaluations with polyscale
        // This is what the verifier does internally

        eprintln!("\n=== Verifying IPA equation ===");
        eprintln!("Equation: c*Q + delta = z1*(sg + b*u) + z2*H");
        eprintln!("Where Q = combined_comm + combined_inner_product*u + lr_prod");

        // Compute RHS = z1*(sg + b*u) + z2*H
        let rhs = {
            let sg_plus_bu =
                (proof.proof.sg.into_group() + u_point.into_group() * b0).into_affine();
            let term1 = sg_plus_bu.into_group() * proof.proof.z1;
            let term2 = h.into_group() * proof.proof.z2;
            (term1 + term2).into_affine()
        };
        if let Some((x, y)) = rhs.to_coordinates() {
            eprintln!("RHS = z1*(sg + b*u) + z2*H: ({x:?}, {y:?})");
        }

        // Compute delta contribution
        if let Some((x, y)) = proof.proof.delta.to_coordinates() {
            eprintln!("delta: ({x:?}, {y:?})");
        }

        // RHS - delta = c*Q, so Q = (RHS - delta) / c
        let rhs_minus_delta = (rhs.into_group() - proof.proof.delta.into_group()).into_affine();
        if let Some((x, y)) = rhs_minus_delta.to_coordinates() {
            eprintln!("RHS - delta (should = c*Q): ({x:?}, {y:?})");
        }

        // Q = (RHS - delta) * c^{-1}
        let c_inv = c.inverse().unwrap_or(G::ScalarField::zero());
        let q_computed = (rhs_minus_delta.into_group() * c_inv).into_affine();
        if let Some((x, y)) = q_computed.to_coordinates() {
            eprintln!("Q (computed from RHS): ({x:?}, {y:?})");
        }

        // Q should equal: combined_comm + combined_inner_product*u + lr_prod
        // So combined_comm = Q - combined_inner_product*u - lr_prod
        let combined_inner_u =
            (u_point.into_group() * oracles_result.combined_inner_product).into_affine();
        let combined_comm_expected =
            (q_computed.into_group() - combined_inner_u.into_group() - lr_prod.into_group())
                .into_affine();
        if let Some((x, y)) = combined_comm_expected.to_coordinates() {
            eprintln!(
                "combined_comm (expected, derived from Q): ({x:?}, {y:?})"
            );
        }

        // Now compute what our FFI function returns
        match combined_polynomial_commitment::<G, EFqSponge, EFrSponge>(
            prover_index,
            proof,
            public_input,
        ) {
            Ok(coords) => {
                eprintln!(
                    "combined_comm (our FFI): ({:?}, {:?})",
                    coords[0], coords[1]
                );

                // Check if they match
                if let Some((expected_x, expected_y)) = combined_comm_expected.to_coordinates() {
                    if coords[0] == expected_x && coords[1] == expected_y {
                        eprintln!("✓ combined_comm MATCHES!");
                    } else {
                        eprintln!("✗ combined_comm DOES NOT MATCH!");
                    }
                }
            }
            Err(e) => {
                eprintln!("combined_polynomial_commitment error: {e:?}");
            }
        }

        eprintln!("=== End Debug ===");
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
/// Returns 12 values: [alpha, beta, gamma, zeta, ft_eval0, v, u,
///                     combined_inner_product, ft_eval1, public_eval_zeta, public_eval_zeta_omega,
///                     fq_digest]
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
/// Returns 12 values: [alpha, beta, gamma, zeta, ft_eval0, v, u,
///                     combined_inner_product, ft_eval1, public_eval_zeta, public_eval_zeta_omega,
///                     fq_digest]
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

/// Extract bulletproof challenges from a Vesta proof (Pallas/Fp circuits).
/// Returns d values where d = domain_log2 (number of IPA rounds).
#[napi]
pub fn pallas_proof_bulletproof_challenges(
    prover_index: &VestaProverIndexExternal,
    proof: &VestaProofExternal,
    public_input: Vec<&VestaFieldExternal>,
) -> Result<Vec<VestaFieldExternal>> {
    let public: Vec<VestaScalarField> = public_input.iter().map(|f| ***f).collect();
    let result = generic::proof_bulletproof_challenges::<
        VestaGroup,
        VestaBaseSponge,
        VestaScalarSponge,
    >(&**prover_index, &**proof, &public)?;
    Ok(result.into_iter().map(External::new).collect())
}

/// Extract bulletproof challenges from a Pallas proof (Vesta/Fq circuits).
/// Returns d values where d = domain_log2 (number of IPA rounds).
#[napi]
pub fn vesta_proof_bulletproof_challenges(
    prover_index: &PallasProverIndexExternal,
    proof: &PallasProofExternal,
    public_input: Vec<&PallasFieldExternal>,
) -> Result<Vec<PallasFieldExternal>> {
    let public: Vec<PallasScalarField> = public_input.iter().map(|f| ***f).collect();
    let result = generic::proof_bulletproof_challenges::<
        PallasGroup,
        PallasBaseSponge,
        PallasScalarSponge,
    >(&**prover_index, &**proof, &public)?;
    Ok(result.into_iter().map(External::new).collect())
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

/// Opaque sponge checkpoint for Pallas circuits.
/// For VestaGroup, G::BaseField = Fq = PallasScalarField (due to Pasta 2-cycle).
pub type PallasSpongeCheckpointExternal =
    External<mina_poseidon::sponge::SpongeCheckpoint<PallasScalarField>>;

/// Opaque sponge checkpoint for Vesta circuits.
/// For PallasGroup, G::BaseField = Fp = VestaScalarField (due to Pasta 2-cycle).
pub type VestaSpongeCheckpointExternal =
    External<mina_poseidon::sponge::SpongeCheckpoint<VestaScalarField>>;

/// Get sponge checkpoint before L/R processing for a Vesta proof (Pallas/Fp circuits).
/// Returns an opaque checkpoint - use accessor functions to get state/mode.
#[napi]
pub fn pallas_sponge_checkpoint(
    prover_index: &VestaProverIndexExternal,
    proof: &VestaProofExternal,
    public_input: Vec<&VestaFieldExternal>,
) -> Result<PallasSpongeCheckpointExternal> {
    let public: Vec<VestaScalarField> = public_input.iter().map(|f| ***f).collect();
    let data = generic::bulletproof_challenge_data::<VestaGroup, VestaBaseSponge, VestaScalarSponge>(
        &**prover_index,
        &**proof,
        &public,
    )?;
    Ok(External::new(data.sponge_checkpoint))
}

/// Get the 3 state field elements from a Pallas sponge checkpoint.
#[napi]
pub fn pallas_sponge_checkpoint_state(
    checkpoint: &PallasSpongeCheckpointExternal,
) -> Vec<PallasFieldExternal> {
    checkpoint
        .state
        .iter()
        .copied()
        .map(External::new)
        .collect()
}

/// Get the sponge mode from a Pallas sponge checkpoint.
/// Returns "Absorbed" or "Squeezed".
#[napi]
pub fn pallas_sponge_checkpoint_mode(checkpoint: &PallasSpongeCheckpointExternal) -> String {
    match checkpoint.sponge_state {
        mina_poseidon::poseidon::SpongeState::Absorbed(_) => "Absorbed".to_string(),
        mina_poseidon::poseidon::SpongeState::Squeezed(_) => "Squeezed".to_string(),
    }
}

/// Get the mode count from a Pallas sponge checkpoint.
#[napi]
pub fn pallas_sponge_checkpoint_mode_count(checkpoint: &PallasSpongeCheckpointExternal) -> u32 {
    match checkpoint.sponge_state {
        mina_poseidon::poseidon::SpongeState::Absorbed(n) => n as u32,
        mina_poseidon::poseidon::SpongeState::Squeezed(n) => n as u32,
    }
}

/// Get sponge checkpoint before L/R processing for a Pallas proof (Vesta/Fq circuits).
/// Returns an opaque checkpoint - use accessor functions to get state/mode.
#[napi]
pub fn vesta_sponge_checkpoint(
    prover_index: &PallasProverIndexExternal,
    proof: &PallasProofExternal,
    public_input: Vec<&PallasFieldExternal>,
) -> Result<VestaSpongeCheckpointExternal> {
    let public: Vec<PallasScalarField> = public_input.iter().map(|f| ***f).collect();
    let data = generic::bulletproof_challenge_data::<
        PallasGroup,
        PallasBaseSponge,
        PallasScalarSponge,
    >(&**prover_index, &**proof, &public)?;
    Ok(External::new(data.sponge_checkpoint))
}

/// Get the 3 state field elements from a Vesta sponge checkpoint.
#[napi]
pub fn vesta_sponge_checkpoint_state(
    checkpoint: &VestaSpongeCheckpointExternal,
) -> Vec<VestaFieldExternal> {
    checkpoint
        .state
        .iter()
        .copied()
        .map(External::new)
        .collect()
}

/// Get the sponge mode from a Vesta sponge checkpoint.
/// Returns "Absorbed" or "Squeezed".
#[napi]
pub fn vesta_sponge_checkpoint_mode(checkpoint: &VestaSpongeCheckpointExternal) -> String {
    match checkpoint.sponge_state {
        mina_poseidon::poseidon::SpongeState::Absorbed(_) => "Absorbed".to_string(),
        mina_poseidon::poseidon::SpongeState::Squeezed(_) => "Squeezed".to_string(),
    }
}

/// Get the mode count from a Vesta sponge checkpoint.
#[napi]
pub fn vesta_sponge_checkpoint_mode_count(checkpoint: &VestaSpongeCheckpointExternal) -> u32 {
    match checkpoint.sponge_state {
        mina_poseidon::poseidon::SpongeState::Absorbed(n) => n as u32,
        mina_poseidon::poseidon::SpongeState::Squeezed(n) => n as u32,
    }
}

/// Get opening proof L/R pairs for a Vesta proof (Pallas/Fp circuits).
/// Returns flat array [L0.x, L0.y, R0.x, R0.y, L1.x, ...]
/// Note: Vesta base field = Pallas scalar field (2-cycle)
#[napi]
pub fn pallas_proof_opening_lr(proof: &VestaProofExternal) -> Vec<PallasFieldExternal> {
    generic::proof_opening_lr::<VestaGroup>(&**proof)
        .into_iter()
        .map(External::new)
        .collect()
}

/// Get opening proof L/R pairs for a Pallas proof (Vesta/Fq circuits).
/// Returns flat array [L0.x, L0.y, R0.x, R0.y, L1.x, ...]
/// Note: Pallas base field = Vesta scalar field (2-cycle)
#[napi]
pub fn vesta_proof_opening_lr(proof: &PallasProofExternal) -> Vec<VestaFieldExternal> {
    generic::proof_opening_lr::<PallasGroup>(&**proof)
        .into_iter()
        .map(External::new)
        .collect()
}

/// Compute lr_prod for a Vesta proof (Pallas/Fp circuits).
/// lr_prod = Σ_i [chal_inv[i] * L_i + chal[i] * R_i]
/// Returns [x, y] coordinates of the result point (in Pallas base field = Fq).
#[napi]
pub fn pallas_proof_lr_prod(
    prover_index: &VestaProverIndexExternal,
    proof: &VestaProofExternal,
    public_input: Vec<&VestaFieldExternal>,
) -> Result<Vec<PallasFieldExternal>> {
    let public: Vec<VestaScalarField> = public_input.iter().map(|f| ***f).collect();
    generic::proof_lr_prod::<VestaGroup, VestaBaseSponge, VestaScalarSponge>(
        &**prover_index,
        &**proof,
        &public,
    )
    .map(|coords| coords.into_iter().map(External::new).collect())
}

/// Compute lr_prod for a Pallas proof (Vesta/Fq circuits).
/// lr_prod = Σ_i [chal_inv[i] * L_i + chal[i] * R_i]
/// Returns [x, y] coordinates of the result point (in Vesta base field = Fp).
#[napi]
pub fn vesta_proof_lr_prod(
    prover_index: &PallasProverIndexExternal,
    proof: &PallasProofExternal,
    public_input: Vec<&PallasFieldExternal>,
) -> Result<Vec<VestaFieldExternal>> {
    let public: Vec<PallasScalarField> = public_input.iter().map(|f| ***f).collect();
    generic::proof_lr_prod::<PallasGroup, PallasBaseSponge, PallasScalarSponge>(
        &**prover_index,
        &**proof,
        &public,
    )
    .map(|coords| coords.into_iter().map(External::new).collect())
}

// ============================================================================
// Opening proof field extractors
// ============================================================================

/// Get opening proof delta for a Vesta proof (Pallas/Fp circuits).
/// Returns [x, y] coordinates of the delta point (in Pallas base field = Fq).
#[napi]
pub fn pallas_proof_opening_delta(proof: &VestaProofExternal) -> Vec<PallasFieldExternal> {
    generic::proof_opening_delta::<VestaGroup>(&**proof)
        .into_iter()
        .map(External::new)
        .collect()
}

/// Get opening proof delta for a Pallas proof (Vesta/Fq circuits).
/// Returns [x, y] coordinates of the delta point (in Vesta base field = Fp).
#[napi]
pub fn vesta_proof_opening_delta(proof: &PallasProofExternal) -> Vec<VestaFieldExternal> {
    generic::proof_opening_delta::<PallasGroup>(&**proof)
        .into_iter()
        .map(External::new)
        .collect()
}

/// Get opening proof sg (challenge polynomial commitment) for a Vesta proof (Pallas/Fp circuits).
/// Returns [x, y] coordinates of the sg point (in Pallas base field = Fq).
#[napi]
pub fn pallas_proof_opening_sg(proof: &VestaProofExternal) -> Vec<PallasFieldExternal> {
    generic::proof_opening_sg::<VestaGroup>(&**proof)
        .into_iter()
        .map(External::new)
        .collect()
}

/// Get opening proof sg (challenge polynomial commitment) for a Pallas proof (Vesta/Fq circuits).
/// Returns [x, y] coordinates of the sg point (in Vesta base field = Fp).
#[napi]
pub fn vesta_proof_opening_sg(proof: &PallasProofExternal) -> Vec<VestaFieldExternal> {
    generic::proof_opening_sg::<PallasGroup>(&**proof)
        .into_iter()
        .map(External::new)
        .collect()
}

/// Get opening proof z1 scalar for a Vesta proof (Pallas/Fp circuits).
/// Returns the z1 scalar in the scalar field (Vesta scalar field = Fp).
#[napi]
pub fn pallas_proof_opening_z1(proof: &VestaProofExternal) -> VestaFieldExternal {
    External::new(generic::proof_opening_z1::<VestaGroup>(&**proof))
}

/// Get opening proof z1 scalar for a Pallas proof (Vesta/Fq circuits).
/// Returns the z1 scalar in the scalar field (Pallas scalar field = Fq).
#[napi]
pub fn vesta_proof_opening_z1(proof: &PallasProofExternal) -> PallasFieldExternal {
    External::new(generic::proof_opening_z1::<PallasGroup>(&**proof))
}

/// Get opening proof z2 scalar for a Vesta proof (Pallas/Fp circuits).
/// Returns the z2 scalar in the scalar field (Vesta scalar field = Fp).
#[napi]
pub fn pallas_proof_opening_z2(proof: &VestaProofExternal) -> VestaFieldExternal {
    External::new(generic::proof_opening_z2::<VestaGroup>(&**proof))
}

/// Get opening proof z2 scalar for a Pallas proof (Vesta/Fq circuits).
/// Returns the z2 scalar in the scalar field (Pallas scalar field = Fq).
#[napi]
pub fn vesta_proof_opening_z2(proof: &PallasProofExternal) -> PallasFieldExternal {
    External::new(generic::proof_opening_z2::<PallasGroup>(&**proof))
}

// ============================================================================
// SRS accessors
// ============================================================================

/// Get the blinding generator H from the SRS for Pallas circuits.
/// Returns [x, y] coordinates of H (in Pallas base field = Fq).
#[napi]
pub fn pallas_prover_index_blinding_generator(
    prover_index: &VestaProverIndexExternal,
) -> Vec<PallasFieldExternal> {
    generic::prover_index_blinding_generator::<VestaGroup>(&**prover_index)
        .into_iter()
        .map(External::new)
        .collect()
}

/// Get the blinding generator H from the SRS for Vesta circuits.
/// Returns [x, y] coordinates of H (in Vesta base field = Fp).
#[napi]
pub fn vesta_prover_index_blinding_generator(
    prover_index: &PallasProverIndexExternal,
) -> Vec<VestaFieldExternal> {
    generic::prover_index_blinding_generator::<PallasGroup>(&**prover_index)
        .into_iter()
        .map(External::new)
        .collect()
}

// ============================================================================
// Combined polynomial commitment
// ============================================================================

/// Compute the combined polynomial commitment for a Vesta proof (Pallas/Fp circuits).
/// Returns [x, y] coordinates of the combined commitment (in Pallas base field = Fq).
#[napi]
pub fn pallas_combined_polynomial_commitment(
    prover_index: &VestaProverIndexExternal,
    proof: &VestaProofExternal,
    public_input: Vec<&VestaFieldExternal>,
) -> Result<Vec<PallasFieldExternal>> {
    let public: Vec<VestaScalarField> = public_input.iter().map(|f| ***f).collect();
    generic::combined_polynomial_commitment::<VestaGroup, VestaBaseSponge, VestaScalarSponge>(
        &**prover_index,
        &**proof,
        &public,
    )
    .map(|coords| coords.into_iter().map(External::new).collect())
}

/// Compute the combined polynomial commitment for a Pallas proof (Vesta/Fq circuits).
/// Returns [x, y] coordinates of the combined commitment (in Vesta base field = Fp).
#[napi]
pub fn vesta_combined_polynomial_commitment(
    prover_index: &PallasProverIndexExternal,
    proof: &PallasProofExternal,
    public_input: Vec<&PallasFieldExternal>,
) -> Result<Vec<VestaFieldExternal>> {
    let public: Vec<PallasScalarField> = public_input.iter().map(|f| ***f).collect();
    generic::combined_polynomial_commitment::<PallasGroup, PallasBaseSponge, PallasScalarSponge>(
        &**prover_index,
        &**proof,
        &public,
    )
    .map(|coords| coords.into_iter().map(External::new).collect())
}

// ============================================================================
// Debug verification tracing
// ============================================================================

/// Run full verification with debug tracing for a Vesta proof (Pallas/Fp circuits).
/// This prints intermediate values to understand the IPA verification.
#[napi]
pub fn pallas_debug_verify(
    prover_index: &VestaProverIndexExternal,
    proof: &VestaProofExternal,
    public_input: Vec<&VestaFieldExternal>,
) {
    let public: Vec<VestaScalarField> = public_input.iter().map(|f| ***f).collect();
    generic::debug_verify::<VestaGroup, VestaBaseSponge, VestaScalarSponge>(
        &**prover_index,
        &**proof,
        &public,
    );
}

/// Run full verification with debug tracing for a Pallas proof (Vesta/Fq circuits).
/// This prints intermediate values to understand the IPA verification.
#[napi]
pub fn vesta_debug_verify(
    prover_index: &PallasProverIndexExternal,
    proof: &PallasProofExternal,
    public_input: Vec<&PallasFieldExternal>,
) {
    let public: Vec<PallasScalarField> = public_input.iter().map(|f| ***f).collect();
    generic::debug_verify::<PallasGroup, PallasBaseSponge, PallasScalarSponge>(
        &**prover_index,
        &**proof,
        &public,
    );
}
