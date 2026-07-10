//! The verifier's scalar side of a real kimchi proof, as a JSON fixture for the Lean
//! linearization transcription (checked by `formal/scripts/check_linearization.lean`).
//!
//! A proof over the shared mixed-gate circuit (`fixture_dump::mixed_circuit`) is created
//! and verified by production code; then the verifier's own oracle derivation
//! (`ProverProof::oracles`) is replayed and the fixture records both the *inputs* of the
//! scalar-side check — challenges, combined evaluations at ζ/ζω, domain constants — and
//! its production *outputs*:
//!
//! * `ft_eval0` — the verifier's closed-form `ft(ζ)` (permutation terms, public input,
//!   boundary quotient, minus the linearization constant term);
//! * `perm_scalar` — `perm_scalars`, the σ-commitment scalar of `f_comm`;
//! * `constant_term` — `PolishToken::evaluate` of `linearization.constant_term`. At this
//!   proof-systems pin every gate selector is evaluated in the proof, so this holds the
//!   ENTIRE gate linearization and `index_terms` is empty (asserted by the empty-object
//!   field);
//! * `gate_combined` — per gate, the token-evaluated `Argument::combined_constraints`
//!   (selector × Σ αᵏ·cₖ), asserted at dump time to sum to `constant_term`.
//!
//! The Lean side recomputes each output from the recorded inputs with its closed-form
//! transcriptions (the `Argument` constraint lists of `formal/Kimchi/Quotient/`) — the
//! token stream never appears in a Lean statement; it is adjudicated here, by value.

use ark_ff::Zero;
use ark_poly::{EvaluationDomain, Polynomial};
use fixture_dump::mixed_circuit;
use groupmap::GroupMap;
use kimchi::{
    circuits::{
        argument::{Argument, ArgumentType},
        berkeley_columns::{BerkeleyChallenges, Column},
        constraints::ConstraintSystem,
        expr::{Cache, Constants, PolishToken},
        gate::GateType,
        polynomials::{
            complete_add::CompleteAdd, endomul_scalar::EndomulScalar, endosclmul::EndosclMul,
            generic::Generic, permutation, poseidon::Poseidon, varbasemul::VarbaseMul,
        },
    },
    curve::KimchiCurve,
    proof::ProverProof,
    prover_index::testing::new_index_for_test,
    verifier::verify,
    verifier_index::VerifierIndex,
};
use mina_curves::pasta::{Fp, Vesta, VestaParameters};
use mina_poseidon::{
    constants::PlonkSpongeConstantsKimchi as SC,
    pasta::FULL_ROUNDS,
    sponge::{DefaultFqSponge, DefaultFrSponge},
};
use poly_commitment::{commitment::PolyComm, SRS as _};
use rand::SeedableRng;
use rand_chacha::ChaCha20Rng;
use serde_json::json;

type BaseSponge = DefaultFqSponge<VestaParameters, SC, FULL_ROUNDS>;
type ScalarSponge = DefaultFrSponge<Fp, SC, FULL_ROUNDS>;

fn fe<F: std::fmt::Display>(x: &F) -> String {
    format!("{}", x)
}

fn index_term_name(col: &Column) -> &'static str {
    match col {
        Column::Index(GateType::CompleteAdd) => "completeAdd",
        Column::Index(GateType::VarBaseMul) => "varBaseMul",
        Column::Index(GateType::EndoMul) => "endoMul",
        Column::Index(GateType::EndoMulScalar) => "endoScalar",
        c => panic!("unexpected linearization index term column: {c:?}"),
    }
}

fn main() {
    let out_dir = std::env::args().nth(1).unwrap_or_else(|| ".".to_string());
    let rng = &mut ChaCha20Rng::from_seed([71u8; 32]);

    // A production proof over the shared mixed-gate circuit.
    let (gates, witness, pub0) = mixed_circuit(rng);
    let index = new_index_for_test::<FULL_ROUNDS, Vesta>(gates, 1);
    index
        .verify(&witness, &[pub0])
        .expect("kimchi row checker rejected the witness");
    let group_map = <Vesta as poly_commitment::commitment::CommitmentCurve>::Map::setup();
    let proof: ProverProof<
        Vesta,
        poly_commitment::ipa::OpeningProof<Vesta, FULL_ROUNDS>,
        FULL_ROUNDS,
    > = ProverProof::create::<BaseSponge, ScalarSponge, _>(&group_map, witness, &[], &index, rng)
        .expect("prover failed");
    let verifier_index: VerifierIndex<FULL_ROUNDS, Vesta, _> = index.verifier_index();
    verify::<FULL_ROUNDS, Vesta, BaseSponge, ScalarSponge, _>(
        &group_map,
        &verifier_index,
        &proof,
        &[pub0],
    )
    .expect("production verifier rejected the fixture proof");

    // The public commitment, exactly as the verifier builds it.
    let public_input: &[Fp] = &[pub0];
    let public_comm = {
        let lgr_comm = verifier_index
            .srs()
            .get_lagrange_basis(verifier_index.domain);
        let com: Vec<_> = lgr_comm.iter().take(verifier_index.public).collect();
        let elm: Vec<_> = public_input.iter().map(|s| -*s).collect();
        let public_comm = PolyComm::<Vesta>::multi_scalar_mul(&com, &elm);
        verifier_index
            .srs()
            .mask_custom(
                public_comm.clone(),
                &public_comm.map(|_| <Fp as ark_ff::One>::one()),
            )
            .unwrap()
            .commitment
    };

    // Replay the verifier's oracle derivation.
    let oracles_res = proof
        .oracles::<BaseSponge, ScalarSponge, _>(&verifier_index, &public_comm, Some(public_input))
        .expect("oracles failed");
    let o = &oracles_res.oracles;
    let evals = proof
        .evals
        .combine(&oracles_res.powers_of_eval_points_for_chunks);
    let zk_rows = verifier_index.zk_rows;

    // The seventh sigma column's evaluation at ζ — the one column the proof does NOT
    // evaluate (its share travels through the commitment channel as perm_scalars ·
    // sigma_comm[6]); interpolated here from the prover index so the Lean side can
    // check the assembled acceptance identity numerically.
    let sigma6_zeta = index.column_evaluations.get().permutation_coefficients8[6]
        .interpolate_by_ref()
        .evaluate(&o.zeta);

    // The production scalar-side outputs.
    let zkpm_zeta = verifier_index
        .permutation_vanishing_polynomial_m()
        .evaluate(&o.zeta);
    let perm_scalar = ConstraintSystem::<Fp>::perm_scalars(
        &evals,
        o.beta,
        o.gamma,
        oracles_res
            .all_alphas
            .get_alphas(ArgumentType::Permutation, permutation::CONSTRAINTS),
        zkpm_zeta,
    );
    let constants = Constants {
        endo_coefficient: verifier_index.endo,
        mds: &<Vesta as KimchiCurve<FULL_ROUNDS>>::sponge_params().mds,
        zk_rows,
    };
    let challenges = BerkeleyChallenges {
        alpha: o.alpha,
        beta: o.beta,
        gamma: o.gamma,
        joint_combiner: Fp::zero(),
    };
    let constant_term = PolishToken::evaluate(
        &verifier_index.linearization.constant_term,
        verifier_index.domain,
        o.zeta,
        &evals,
        &constants,
        &challenges,
    )
    .expect("constant term evaluation failed");
    // Per-gate combined constraints (selector × Σ αᵏ·cₖ — `combined_constraints`
    // multiplies the gate's selector column itself), token-evaluated on the same inputs
    // — the per-gate targets for the Lean closed forms, and a production-side
    // decomposition check of the constant term.
    let gate_combined: Vec<(&'static str, Fp)> = {
        let alphas = &oracles_res.all_alphas;
        let mut cache = Cache::default();
        macro_rules! gate_term {
            ($t:ty) => {
                PolishToken::evaluate(
                    &<$t>::combined_constraints(alphas, &mut cache).to_polish(),
                    verifier_index.domain,
                    o.zeta,
                    &evals,
                    &constants,
                    &challenges,
                )
                .expect("gate combined constraints evaluation failed")
            };
        }
        vec![
            ("generic", gate_term!(Generic<Fp>)),
            ("poseidon", gate_term!(Poseidon<Fp>)),
            ("completeAdd", gate_term!(CompleteAdd<Fp>)),
            ("varBaseMul", gate_term!(VarbaseMul<Fp>)),
            ("endoMul", gate_term!(EndosclMul<Fp>)),
            ("endoScalar", gate_term!(EndomulScalar<Fp>)),
        ]
    };
    // Decomposition check: the per-gate terms (selector already inside
    // `combined_constraints`) must sum to the constant term the verifier subtracts.
    {
        let sum: Fp = gate_combined.iter().map(|(_, g)| *g).sum();
        assert_eq!(
            sum, constant_term,
            "gate combined-constraint terms do not sum to the constant term"
        );
    }
    let index_terms: Vec<(&'static str, Fp)> = verifier_index
        .linearization
        .index_terms
        .iter()
        .map(|(col, tokens)| {
            let scalar = PolishToken::evaluate(
                tokens,
                verifier_index.domain,
                o.zeta,
                &evals,
                &constants,
                &challenges,
            )
            .expect("index term evaluation failed");
            (index_term_name(col), scalar)
        })
        .collect();

    // Inputs: the combined evaluations the scalar side reads, per column at ζ and ζω.
    let pe = |e: &kimchi::proof::PointEvaluations<Fp>| json!([fe(&e.zeta), fe(&e.zeta_omega)]);
    let fixture = json!({
        "curve": "vesta",
        "n": verifier_index.domain.size().to_string(),
        "zk_rows": zk_rows.to_string(),
        "omega": fe(&verifier_index.domain.group_gen),
        "shifts": verifier_index.shift.iter().map(fe).collect::<Vec<_>>(),
        "endo": fe(&verifier_index.endo),
        "alpha": fe(&o.alpha),
        "beta": fe(&o.beta),
        "gamma": fe(&o.gamma),
        "zeta": fe(&o.zeta),
        "zkpm_zeta": fe(&zkpm_zeta),
        "public_evals": [
            oracles_res.public_evals[0].iter().map(fe).collect::<Vec<_>>(),
            oracles_res.public_evals[1].iter().map(fe).collect::<Vec<_>>(),
        ],
        "w": evals.w.iter().map(pe).collect::<Vec<_>>(),
        "z": pe(&evals.z),
        "s": evals.s.iter().map(pe).collect::<Vec<_>>(),
        "coefficients": evals.coefficients.iter().map(pe).collect::<Vec<_>>(),
        "generic_selector": pe(&evals.generic_selector),
        "poseidon_selector": pe(&evals.poseidon_selector),
        "complete_add_selector": pe(&evals.complete_add_selector),
        "mul_selector": pe(&evals.mul_selector),
        "emul_selector": pe(&evals.emul_selector),
        "endomul_scalar_selector": pe(&evals.endomul_scalar_selector),
        "ft_eval1": fe(&proof.ft_eval1),
        "sigma6_zeta": fe(&sigma6_zeta),
        // the production outputs the Lean closed forms must reproduce
        "ft_eval0": fe(&oracles_res.ft_eval0),
        "perm_scalar": fe(&perm_scalar),
        "constant_term": fe(&constant_term),
        "gate_combined": gate_combined.iter()
            .map(|(name, s)| (name.to_string(), json!(fe(s))))
            .collect::<serde_json::Map<_, _>>(),
        "index_terms": index_terms.iter()
            .map(|(name, s)| (name.to_string(), json!(fe(s))))
            .collect::<serde_json::Map<_, _>>(),
    });

    let path = format!("{out_dir}/linearization_vesta.json");
    std::fs::write(&path, serde_json::to_string_pretty(&fixture).unwrap()).unwrap();
    println!(
        "linearization: {} index terms, production verify accepts; wrote {path}",
        index_terms.len()
    );
}
