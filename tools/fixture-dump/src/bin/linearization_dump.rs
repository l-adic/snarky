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
use fixture_dump::{
    emul_circuit, emul_index, mixed_circuit, mixed_circuit_fq, mixed_index, mixed_index_over,
};
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
    verifier::verify,
    verifier_index::VerifierIndex,
};
use mina_curves::pasta::{Fp, Fq, Pallas, PallasParameters, Vesta, VestaParameters};
use mina_poseidon::{
    constants::PlonkSpongeConstantsKimchi as SC,
    pasta::FULL_ROUNDS,
    sponge::{DefaultFqSponge, DefaultFrSponge},
};
use poly_commitment::{commitment::PolyComm, SRS as _};
use rand::SeedableRng;
use rand_chacha::ChaCha20Rng;
use serde_json::json;

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

/// The dump, per curve: `$G` is the proof's curve, `$F` its scalar field (the circuit
/// field), `$GParams` the sponge's curve parameters.
macro_rules! dump_linearization {
    ($modname:ident, $curve_str:literal, $G:ty, $GParams:ty, $F:ty) => {
        mod $modname {
            use super::*;

            type BaseSponge = DefaultFqSponge<$GParams, SC, FULL_ROUNDS>;
            type ScalarSponge = DefaultFrSponge<$F, SC, FULL_ROUNDS>;

            /// One linearization fixture: a production proof over `index`, with its scalar side
            /// recorded. `public` is the circuit's public input (empty for the scalar-mul circuit).
            pub fn run(
                out_dir: &str,
                rng: &mut ChaCha20Rng,
                index: kimchi::prover_index::ProverIndex<
                    FULL_ROUNDS,
                    $G,
                    poly_commitment::ipa::SRS<$G>,
                >,
                witness: [Vec<$F>; 15],
                public: Vec<$F>,
                fname: &str,
            ) {
                index
                    .verify(&witness, &public)
                    .expect("kimchi row checker rejected the witness");
                let group_map = <$G as poly_commitment::commitment::CommitmentCurve>::Map::setup();
                let proof: ProverProof<
                    $G,
                    poly_commitment::ipa::OpeningProof<$G, FULL_ROUNDS>,
                    FULL_ROUNDS,
                > = ProverProof::create::<BaseSponge, ScalarSponge, _>(&group_map, witness, &[], &index, rng)
                    .expect("prover failed");
                let verifier_index: VerifierIndex<FULL_ROUNDS, $G, _> = index.verifier_index();
                verify::<FULL_ROUNDS, $G, BaseSponge, ScalarSponge, _>(
                    &group_map,
                    &verifier_index,
                    &proof,
                    &public,
                )
                .expect("production verifier rejected the fixture proof");

                // The public commitment, exactly as the verifier builds it.
                let public_input: &[$F] = &public;
                let public_comm = {
                    let lgr_comm = verifier_index
                        .srs()
                        .get_lagrange_basis(verifier_index.domain);
                    let com: Vec<_> = lgr_comm.iter().take(verifier_index.public).collect();
                    let elm: Vec<_> = public_input.iter().map(|s| -*s).collect();
                    let public_comm = PolyComm::<$G>::multi_scalar_mul(&com, &elm);
                    verifier_index
                        .srs()
                        .mask_custom(
                            public_comm.clone(),
                            &public_comm.map(|_| <$F as ark_ff::One>::one()),
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
                let perm_scalar = ConstraintSystem::<$F>::perm_scalars(
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
                    mds: &<$G as KimchiCurve<FULL_ROUNDS>>::sponge_params().mds,
                    zk_rows,
                };
                let challenges = BerkeleyChallenges {
                    alpha: o.alpha,
                    beta: o.beta,
                    gamma: o.gamma,
                    joint_combiner: <$F as Zero>::zero(),
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
                let gate_combined: Vec<(&'static str, $F)> = {
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
                        ("generic", gate_term!(Generic<$F>)),
                        ("poseidon", gate_term!(Poseidon<$F>)),
                        ("completeAdd", gate_term!(CompleteAdd<$F>)),
                        ("varBaseMul", gate_term!(VarbaseMul<$F>)),
                        ("endoMul", gate_term!(EndosclMul<$F>)),
                        ("endoScalar", gate_term!(EndomulScalar<$F>)),
                    ]
                };
                // Decomposition check: the per-gate terms (selector already inside
                // `combined_constraints`) must sum to the constant term the verifier subtracts.
                {
                    let sum: $F = gate_combined.iter().map(|(_, g)| *g).sum();
                    assert_eq!(
                        sum, constant_term,
                        "gate combined-constraint terms do not sum to the constant term"
                    );
                }
                let index_terms: Vec<(&'static str, $F)> = verifier_index
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
                let pe = |e: &kimchi::proof::PointEvaluations<$F>| json!([fe(&e.zeta), fe(&e.zeta_omega)]);
                let fixture = json!({
                    "curve": $curve_str,
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

                let path = format!("{out_dir}/{fname}");
                std::fs::write(&path, serde_json::to_string_pretty(&fixture).unwrap()).unwrap();
                let live: Vec<&str> = gate_combined
                    .iter()
                    .filter(|(_, v)| !v.is_zero())
                    .map(|(n, _)| *n)
                    .collect();
                println!(
                    "linearization: {} index terms, live gate terms {live:?}, production verify \
                     accepts; wrote {path}",
                    index_terms.len()
                );
            }
        }
    };
}

dump_linearization!(vesta, "vesta", Vesta, VestaParameters, Fp);
dump_linearization!(pallas, "pallas", Pallas, PallasParameters, Fq);

fn main() {
    let out_dir = std::env::args().nth(1).unwrap_or_else(|| ".".to_string());
    // The shared mixed-gate circuit — same seed as `kimchi_proof_dump`, so the two
    // fixtures describe the same proof. Its `emul`/`mul` selectors are identically zero,
    // so its per-gate targets for those two gates are `0 = 0` (external-audit R-1).
    {
        let rng = &mut ChaCha20Rng::from_seed([71u8; 32]);
        let (gates, witness, pub0) = mixed_circuit(rng);
        vesta::run(
            &out_dir,
            rng,
            mixed_index(gates),
            witness,
            vec![pub0],
            "linearization_vesta.json",
        );
    }
    // The scalar-multiplication circuit (same one `kimchi_proof_dump_emul` proves): LIVE
    // EndoMul and VarBaseMul selectors, so the per-gate combined-constraint targets for
    // exactly the two gates finding V-1 concerned are non-zero and adjudicated
    // gate-by-gate, rather than only end-to-end through whole-proof acceptance.
    {
        let rng = &mut ChaCha20Rng::from_seed([83u8; 32]);
        let (gates, witness) = emul_circuit(rng);
        vesta::run(
            &out_dir,
            rng,
            emul_index(gates),
            witness,
            vec![],
            "linearization_vesta_emul.json",
        );
    }
    // The Pallas twin of the mixed-gate circuit (`mixed_circuit_fq`, same construction
    // and rng draw order over `Fq`): the scalar side of a proof verified in Pallas's
    // scalar field, which is what anchors the `Fq` token stream's endomorphism constant
    // and MDS matrix — EndoScalar's large literals differ between the two Pasta fields,
    // so a Vesta-side fixture cannot witness them.
    {
        let rng = &mut ChaCha20Rng::from_seed([71u8; 32]);
        let (gates, witness, pub0) = mixed_circuit_fq(rng);
        pallas::run(
            &out_dir,
            rng,
            mixed_index_over::<Pallas>(gates, None),
            witness,
            vec![pub0],
            "linearization_pallas.json",
        );
    }
}
