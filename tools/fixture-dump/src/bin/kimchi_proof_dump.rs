//! A complete kimchi wire proof + verifier key as a JSON fixture for the Lean
//! executable verifier (`formal/Kimchi/Verifier/Kimchi.lean`, checked by
//! `formal/scripts/check_kimchi_verifier.lean`).
//!
//! The proof is over the shared mixed-gate circuit (`fixture_dump::mixed_circuit`),
//! created and accepted by production code, with the SAME seed as
//! `linearization_dump` — the two fixtures describe the same proof, so the scalar-side
//! values cross-check. Everything the wire protocol carries is dumped uncombined
//! (`nc = 1`: every evaluation is a one-chunk array, every commitment a single point
//! except the 7-chunk `t`), plus the verifier-key data the executable verifier
//! consumes: the committed columns, the domain/permutation constants, the
//! Lagrange-basis commitments for the public polynomial, BOTH endo coefficients
//! (`endo` — the gate/expr constant; `endo_r` — the scalar-challenge expansion
//! coefficient), and the verifier-index digest (taken as wire input by the Lean
//! verifier; transcribing `VerifierIndex::digest()`'s absorb schedule is a declared
//! deferral there).
//!
//! Two fixtures from the ONE proof, differing only in whether the proof-carried public
//! evaluations `evals.public` are recorded:
//!
//! * `kimchi_proof_vesta.json` — WITHOUT `evals_public`. This mirrors the DEPLOYED wire
//!   representation: o1js / the OCaml `to_repr` drop the public-eval chunks at `nc = 1`,
//!   and the verifier then recomputes them barycentrically from the public input
//!   (verifier.rs:336–379). The Lean verifier's `PubEvalSrc.barycentric` branch.
//! * `kimchi_proof_vesta_pub.json` — WITH `evals_public`. The Rust `ProverProof::create`
//!   ALWAYS populates `evals.public = Some(..)` (prover.rs:1048), even at `nc = 1`, and
//!   the verifier's FIRST branch uses carried evaluations at ANY chunk count
//!   (verifier.rs:332). So the carried-at-`nc = 1` case IS production-reachable — this
//!   fixture records it straight off the real proof (same production verify asserted),
//!   exercising the Lean verifier's `PubEvalSrc.carried` branch at one chunk. For a
//!   genuine proof the carried values equal the barycentric ones, so both fixtures
//!   verify against the same transcript.

use ark_poly::EvaluationDomain;
use fixture_dump::{mixed_circuit, mixed_index};
use groupmap::GroupMap;
use kimchi::{
    curve::KimchiCurve, proof::ProverProof, verifier::verify, verifier_index::VerifierIndex,
};
use mina_curves::pasta::{Fp, Vesta, VestaParameters};
use mina_poseidon::{
    constants::PlonkSpongeConstantsKimchi as SC,
    pasta::FULL_ROUNDS,
    sponge::{DefaultFqSponge, DefaultFrSponge},
};
use poly_commitment::SRS as _;
use rand::SeedableRng;
use rand_chacha::ChaCha20Rng;
use serde_json::json;

type BaseSponge = DefaultFqSponge<VestaParameters, SC, FULL_ROUNDS>;
type ScalarSponge = DefaultFrSponge<Fp, SC, FULL_ROUNDS>;

fn fe<F: std::fmt::Display>(x: &F) -> String {
    format!("{}", x)
}

fn pt(g: &Vesta) -> serde_json::Value {
    use ark_ec::AffineRepr;
    assert!(!g.is_zero(), "fixture point unexpectedly at infinity");
    json!([fe(&g.x), fe(&g.y)])
}

/// A one-chunk `PolyComm` as a bare point.
fn comm1(c: &poly_commitment::commitment::PolyComm<Vesta>) -> serde_json::Value {
    assert_eq!(c.chunks.len(), 1, "expected a one-chunk commitment");
    pt(&c.chunks[0])
}

/// A `[zeta, zeta_omega]` evaluation pair, one chunk each.
fn pe(e: &kimchi::proof::PointEvaluations<Vec<Fp>>) -> serde_json::Value {
    assert_eq!(e.zeta.len(), 1, "expected one-chunk evaluations");
    assert_eq!(e.zeta_omega.len(), 1, "expected one-chunk evaluations");
    json!([fe(&e.zeta[0]), fe(&e.zeta_omega[0])])
}

fn main() {
    let out_dir = std::env::args().nth(1).unwrap_or_else(|| ".".to_string());
    // SAME seed as linearization_dump: the two fixtures describe the same proof.
    let rng = &mut ChaCha20Rng::from_seed([71u8; 32]);

    let (gates, witness, pub0) = mixed_circuit(rng);
    let index = mixed_index(gates);
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
    assert!(
        proof.prev_challenges.is_empty(),
        "fixture proof unexpectedly carries recursion challenges"
    );

    let digest = verifier_index.digest::<BaseSponge>();
    let (_, endo_r) = Vesta::endos();
    let lgr = verifier_index
        .srs()
        .get_lagrange_basis(verifier_index.domain);
    let ev = &proof.evals;

    let fixture = json!({
        "curve": "vesta",
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
        // the FULL basis (not just the public prefix): the VK-correspondence check
        // MSMs every committed column's values against it
        "lagrange_basis": lgr.iter().map(comm1).collect::<Vec<_>>(),
        "sigma_comm": verifier_index.sigma_comm.iter().map(comm1).collect::<Vec<_>>(),
        "coefficients_comm": verifier_index.coefficients_comm.iter()
            .map(comm1).collect::<Vec<_>>(),
        "generic_comm": comm1(&verifier_index.generic_comm),
        "psm_comm": comm1(&verifier_index.psm_comm),
        "complete_add_comm": comm1(&verifier_index.complete_add_comm),
        "mul_comm": comm1(&verifier_index.mul_comm),
        "emul_comm": comm1(&verifier_index.emul_comm),
        "endomul_scalar_comm": comm1(&verifier_index.endomul_scalar_comm),
        // --- public input ---
        "public": [fe(&pub0)],
        // --- proof ---
        "w_comm": proof.commitments.w_comm.iter().map(comm1).collect::<Vec<_>>(),
        "z_comm": comm1(&proof.commitments.z_comm),
        "t_comm": proof.commitments.t_comm.chunks.iter().map(pt).collect::<Vec<_>>(),
        "evals_w": ev.w.iter().map(pe).collect::<Vec<_>>(),
        "evals_z": pe(&ev.z),
        "evals_s": ev.s.iter().map(pe).collect::<Vec<_>>(),
        "evals_coefficients": ev.coefficients.iter().map(pe).collect::<Vec<_>>(),
        "evals_generic_selector": pe(&ev.generic_selector),
        "evals_poseidon_selector": pe(&ev.poseidon_selector),
        "evals_complete_add_selector": pe(&ev.complete_add_selector),
        "evals_mul_selector": pe(&ev.mul_selector),
        "evals_emul_selector": pe(&ev.emul_selector),
        "evals_endomul_scalar_selector": pe(&ev.endomul_scalar_selector),
        "ft_eval1": fe(&proof.ft_eval1),
        "lr": proof.proof.lr.iter().map(|(l, r)| json!([pt(l), pt(r)]))
            .collect::<Vec<_>>(),
        "delta": pt(&proof.proof.delta),
        "z1": fe(&proof.proof.z1),
        "z2": fe(&proof.proof.z2),
        "sg": pt(&proof.proof.sg),
    });

    let path = format!("{out_dir}/kimchi_proof_vesta.json");
    std::fs::write(&path, serde_json::to_string_pretty(&fixture).unwrap()).unwrap();

    // The carried-public twin: the SAME proof, but recording the proof-carried public
    // evaluations the Rust prover always produces (verifier.rs uses them at any nc). The
    // Lean verifier's `PubEvalSrc.carried` branch at one chunk.
    let ev_public = ev
        .public
        .as_ref()
        .expect("ProverProof::create should always populate evals.public");
    let mut fixture_pub = fixture;
    fixture_pub
        .as_object_mut()
        .unwrap()
        .insert("evals_public".to_string(), pe(ev_public));
    let pub_path = format!("{out_dir}/kimchi_proof_vesta_pub.json");
    std::fs::write(
        &pub_path,
        serde_json::to_string_pretty(&fixture_pub).unwrap(),
    )
    .unwrap();

    println!(
        "kimchi proof: n={} t chunks={}, production verify accepts; wrote {path} and \
         {pub_path} (carried evals.public twin)",
        verifier_index.domain.size(),
        proof.commitments.t_comm.chunks.len()
    );
}
