//! The CHUNKED (`nc = 2`) twin of `kimchi_proof_dump`: a complete kimchi wire proof +
//! verifier key over an SRS of HALF the domain size (`override_srs_size = n / 2`, the
//! `prover_index.rs` test hook), so every degree-`< n` column is committed and
//! evaluated in two `max_poly_size`-width chunks — the production chunked regime the
//! generalized Lean verifier (`formal/kimchi/Kimchi/Verifier/Kimchi.lean`) is checked
//! against. Same mixed circuit and same seed as the one-chunk fixture; both Pasta
//! curves are dumped (`kimchi_proof_vesta_nc2.json`, `kimchi_proof_pallas_nc2.json`).
//!
//! Everything the wire protocol carries is dumped uncombined, as chunk ARRAYS: each
//! commitment field is the `PolyComm`'s chunk vector (`nc` points; `t` up to `7·nc`),
//! each evaluation is `[[ζ-chunks], [ζω-chunks]]`, and — new at `nc > 1` — the
//! proof-carried public evaluations `evals.public` (the production verifier REQUIRES
//! them when `chunk_size > 1`, verifier.rs `MissingPublicInputEvaluation`; the
//! barycentric fallback exists only at one chunk). Values are read straight off the
//! kimchi proof types: o1js-style `to_repr` serialization drops public-eval chunks.

// The json! literal below is large; the default limit trips inside serde_json's
// recursive expansion.
#![recursion_limit = "256"]

use ark_poly::EvaluationDomain;
use fixture_dump::{mixed_circuit, mixed_circuit_fq, mixed_index_over};
use groupmap::GroupMap;
use kimchi::{
    curve::KimchiCurve, proof::ProverProof, verifier::verify, verifier_index::VerifierIndex,
};
use mina_poseidon::{
    constants::PlonkSpongeConstantsKimchi as SC,
    pasta::FULL_ROUNDS,
    sponge::{DefaultFqSponge, DefaultFrSponge},
};
use poly_commitment::SRS as _;
use rand::SeedableRng;
use rand_chacha::ChaCha20Rng;
use serde_json::json;

fn fe<F: std::fmt::Display>(x: &F) -> String {
    format!("{}", x)
}

macro_rules! dump_nc2 {
    ($modname:ident, $curve_str:literal, $G:ty, $GParams:ty, $F:ty, $circuit:path) => {
        mod $modname {
            use super::*;

            type BaseSponge = DefaultFqSponge<$GParams, SC, FULL_ROUNDS>;
            type ScalarSponge = DefaultFrSponge<$F, SC, FULL_ROUNDS>;

            fn pt(g: &$G) -> serde_json::Value {
                use ark_ec::AffineRepr;
                assert!(!g.is_zero(), "fixture point unexpectedly at infinity");
                json!([fe(&g.x), fe(&g.y)])
            }

            /// A `PolyComm` as its chunk vector (exactly `nc` points).
            fn commc(
                c: &poly_commitment::commitment::PolyComm<$G>,
                nc: usize,
            ) -> serde_json::Value {
                assert_eq!(c.chunks.len(), nc, "expected an {nc}-chunk commitment");
                json!(c.chunks.iter().map(pt).collect::<Vec<_>>())
            }

            /// An evaluation as `[[ζ-chunks], [ζω-chunks]]` (exactly `nc` each).
            fn pec(
                e: &kimchi::proof::PointEvaluations<Vec<$F>>,
                nc: usize,
            ) -> serde_json::Value {
                assert_eq!(e.zeta.len(), nc, "expected {nc}-chunk evaluations");
                assert_eq!(e.zeta_omega.len(), nc, "expected {nc}-chunk evaluations");
                json!([
                    e.zeta.iter().map(fe).collect::<Vec<_>>(),
                    e.zeta_omega.iter().map(fe).collect::<Vec<_>>(),
                ])
            }

            pub fn run(out_dir: &str) {
                // SAME seed as the one-chunk fixtures: the same circuit and witness,
                // re-proved over the half-size SRS.
                let rng = &mut ChaCha20Rng::from_seed([71u8; 32]);
                let (gates, witness, pub0) = $circuit(rng);
                // Probe the chunk-free domain size, then rebuild at half of it.
                let n = mixed_index_over::<$G>(gates.clone(), None)
                    .cs
                    .domain
                    .d1
                    .size();
                let index = mixed_index_over::<$G>(gates, Some(n / 2));
                assert_eq!(
                    index.cs.domain.d1.size(),
                    n,
                    "domain grew under the chunked zk_rows; fixture story assumes nc = 2"
                );
                index
                    .verify(&witness, &[pub0])
                    .expect("kimchi row checker rejected the witness");
                let group_map =
                    <$G as poly_commitment::commitment::CommitmentCurve>::Map::setup();
                let proof: ProverProof<
                    $G,
                    poly_commitment::ipa::OpeningProof<$G, FULL_ROUNDS>,
                    FULL_ROUNDS,
                > = ProverProof::create::<BaseSponge, ScalarSponge, _>(
                    &group_map, witness, &[], &index, rng,
                )
                .expect("prover failed");
                let verifier_index: VerifierIndex<FULL_ROUNDS, $G, _> = index.verifier_index();
                verify::<FULL_ROUNDS, $G, BaseSponge, ScalarSponge, _>(
                    &group_map,
                    &verifier_index,
                    &proof,
                    &[pub0],
                )
                .expect("production verifier rejected the fixture proof");
                assert!(
                    proof.prev_challenges.is_empty(),
                    "fixture proof unexpectedly carries recursion challenges"
                );
                let nc = n / verifier_index.max_poly_size;
                assert_eq!(nc, 2, "expected a two-chunk fixture");
                assert!(
                    proof.commitments.t_comm.chunks.len() <= 7 * nc,
                    "quotient chunk count exceeds 7·nc"
                );

                let digest = verifier_index.digest::<BaseSponge>();
                let (_, endo_r) = <$G as KimchiCurve<FULL_ROUNDS>>::endos();
                let lgr = verifier_index
                    .srs()
                    .get_lagrange_basis(verifier_index.domain);
                let ev = &proof.evals;
                let ev_public = ev
                    .public
                    .as_ref()
                    .expect("chunked proof must carry public evaluations");

                let fixture = json!({
                    "curve": $curve_str,
                    // --- verifier key ---
                    "n": verifier_index.domain.size().to_string(),
                    "zk_rows": verifier_index.zk_rows.to_string(),
                    "max_poly_size": verifier_index.max_poly_size.to_string(),
                    "public_count": verifier_index.public.to_string(),
                    "omega": fe(&verifier_index.domain.group_gen),
                    "shifts": verifier_index.shift.iter().map(fe).collect::<Vec<_>>(),
                    "endo": fe(&verifier_index.endo),
                    "endo_r": fe(endo_r),
                    "digest": fe(&digest),
                    "srs_g": verifier_index.srs().g.iter().map(pt).collect::<Vec<_>>(),
                    "srs_h": pt(&verifier_index.srs().h),
                    // the FULL basis (not just the public prefix): the VK-correspondence
                    // check MSMs every committed column's values against it
                    "lagrange_basis": lgr.iter().map(|c| commc(c, nc)).collect::<Vec<_>>(),
                    "sigma_comm": verifier_index.sigma_comm.iter()
                        .map(|c| commc(c, nc)).collect::<Vec<_>>(),
                    "coefficients_comm": verifier_index.coefficients_comm.iter()
                        .map(|c| commc(c, nc)).collect::<Vec<_>>(),
                    "generic_comm": commc(&verifier_index.generic_comm, nc),
                    "psm_comm": commc(&verifier_index.psm_comm, nc),
                    "complete_add_comm": commc(&verifier_index.complete_add_comm, nc),
                    "mul_comm": commc(&verifier_index.mul_comm, nc),
                    "emul_comm": commc(&verifier_index.emul_comm, nc),
                    "endomul_scalar_comm": commc(&verifier_index.endomul_scalar_comm, nc),
                    // --- public input ---
                    "public": [fe(&pub0)],
                    // --- proof ---
                    "w_comm": proof.commitments.w_comm.iter()
                        .map(|c| commc(c, nc)).collect::<Vec<_>>(),
                    "z_comm": commc(&proof.commitments.z_comm, nc),
                    "t_comm": proof.commitments.t_comm.chunks.iter().map(pt)
                        .collect::<Vec<_>>(),
                    "evals_public": pec(ev_public, nc),
                    "evals_w": ev.w.iter().map(|e| pec(e, nc)).collect::<Vec<_>>(),
                    "evals_z": pec(&ev.z, nc),
                    "evals_s": ev.s.iter().map(|e| pec(e, nc)).collect::<Vec<_>>(),
                    "evals_coefficients": ev.coefficients.iter()
                        .map(|e| pec(e, nc)).collect::<Vec<_>>(),
                    "evals_generic_selector": pec(&ev.generic_selector, nc),
                    "evals_poseidon_selector": pec(&ev.poseidon_selector, nc),
                    "evals_complete_add_selector": pec(&ev.complete_add_selector, nc),
                    "evals_mul_selector": pec(&ev.mul_selector, nc),
                    "evals_emul_selector": pec(&ev.emul_selector, nc),
                    "evals_endomul_scalar_selector": pec(&ev.endomul_scalar_selector, nc),
                    "ft_eval1": fe(&proof.ft_eval1),
                    "lr": proof.proof.lr.iter().map(|(l, r)| json!([pt(l), pt(r)]))
                        .collect::<Vec<_>>(),
                    "delta": pt(&proof.proof.delta),
                    "z1": fe(&proof.proof.z1),
                    "z2": fe(&proof.proof.z2),
                    "sg": pt(&proof.proof.sg),
                });

                let path = format!("{out_dir}/kimchi_proof_{}_nc2.json", $curve_str);
                std::fs::write(&path, serde_json::to_string_pretty(&fixture).unwrap())
                    .unwrap();
                println!(
                    "kimchi proof ({}, nc=2): n={} max_poly_size={} zk_rows={} t chunks={}, \
                     production verify accepts; wrote {path}",
                    $curve_str,
                    verifier_index.domain.size(),
                    verifier_index.max_poly_size,
                    verifier_index.zk_rows,
                    proof.commitments.t_comm.chunks.len()
                );
            }
        }
    };
}

dump_nc2!(
    vesta_nc2,
    "vesta",
    mina_curves::pasta::Vesta,
    mina_curves::pasta::VestaParameters,
    mina_curves::pasta::Fp,
    mixed_circuit
);
dump_nc2!(
    pallas_nc2,
    "pallas",
    mina_curves::pasta::Pallas,
    mina_curves::pasta::PallasParameters,
    mina_curves::pasta::Fq,
    mixed_circuit_fq
);

fn main() {
    let out_dir = std::env::args().nth(1).unwrap_or_else(|| ".".to_string());
    vesta_nc2::run(&out_dir);
    pallas_nc2::run(&out_dir);
}
