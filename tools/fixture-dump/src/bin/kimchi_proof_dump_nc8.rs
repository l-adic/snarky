//! A HIGHER-chunk (`nc = 8`) kimchi wire proof + verifier key — the nc > 2 parameter
//! coverage the Lean executable verifier (`formal/kimchi/Kimchi/Verifier/Kimchi.lean`)
//! needs beyond the `nc = 1` / `nc = 2` fixtures.
//!
//! The same mixed circuit and seed as the `nc = 2` twins, re-indexed over an
//! `max_poly_size = 8` SRS (`override_srs_size = Some(8)`, the `prover_index.rs` test
//! hook). At `max_poly_size = 8` the chunked `zk_rows` (19) push the padded circuit past
//! `n = 32`, so the constraint system's domain grows to `n = 64`; the chunk count is then
//! `n / max_poly_size = 8`, with a full `7·nc = 56`-chunk quotient. This is the natural
//! nc > 2 configuration for this circuit: `nc = 3` is UNPRODUCIBLE (a non-power-of-two
//! `max_poly_size` misaligns the segment chunking, and the production prover rejects it
//! with `WrongBlinders`), and `nc = 4` would need a larger circuit to hold a 64-row
//! domain at `max_poly_size = 16`. Note `max_poly_size = n / 8 ≠ n / 2`, so this fixture
//! also covers the `max_poly_size ≠ n/2` shape the `nc = 2` twins do not.
//!
//! Everything the wire protocol carries is dumped uncombined, as chunk ARRAYS (the same
//! encoding as `kimchi_proof_dump_nc2`): each commitment field is the `PolyComm`'s chunk
//! vector, each evaluation is `[[ζ-chunks], [ζω-chunks]]`, and the proof-carried public
//! evaluations `evals.public` (REQUIRED at `nc > 1`). The full production prove + verify
//! is asserted at dump time (offline via the cached SRS).

#![recursion_limit = "256"]

use ark_poly::EvaluationDomain;
use fixture_dump::{mixed_circuit, mixed_index_over};
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

/// The SRS window forced at dump time: `max_poly_size = 8` (a power of two, so the
/// segment chunking aligns and the prover accepts).
const OVERRIDE_SRS_SIZE: usize = 8;

fn fe<F: std::fmt::Display>(x: &F) -> String {
    format!("{}", x)
}

fn pt(g: &Vesta) -> serde_json::Value {
    use ark_ec::AffineRepr;
    assert!(!g.is_zero(), "fixture point unexpectedly at infinity");
    json!([fe(&g.x), fe(&g.y)])
}

/// A `PolyComm` as its chunk vector (exactly `nc` points).
fn commc(c: &poly_commitment::commitment::PolyComm<Vesta>, nc: usize) -> serde_json::Value {
    assert_eq!(c.chunks.len(), nc, "expected an {nc}-chunk commitment");
    json!(c.chunks.iter().map(pt).collect::<Vec<_>>())
}

/// An evaluation as `[[ζ-chunks], [ζω-chunks]]` (exactly `nc` each).
fn pec(e: &kimchi::proof::PointEvaluations<Vec<Fp>>, nc: usize) -> serde_json::Value {
    assert_eq!(e.zeta.len(), nc, "expected {nc}-chunk evaluations");
    assert_eq!(e.zeta_omega.len(), nc, "expected {nc}-chunk evaluations");
    json!([
        e.zeta.iter().map(fe).collect::<Vec<_>>(),
        e.zeta_omega.iter().map(fe).collect::<Vec<_>>(),
    ])
}

fn main() {
    let out_dir = std::env::args().nth(1).unwrap_or_else(|| ".".to_string());
    // SAME seed as the nc = 2 twins: the same circuit and witness, re-proved over the
    // narrower SRS.
    let rng = &mut ChaCha20Rng::from_seed([71u8; 32]);
    let (gates, witness, pub0) = mixed_circuit(rng);
    let index = mixed_index_over::<Vesta>(gates, Some(OVERRIDE_SRS_SIZE));
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
    let n = verifier_index.domain.size();
    let nc = n / verifier_index.max_poly_size;
    assert!(nc > 2, "expected an nc > 2 fixture, got nc = {nc}");
    assert!(
        proof.commitments.t_comm.chunks.len() <= 7 * nc,
        "quotient chunk count exceeds 7·nc"
    );

    let digest = verifier_index.digest::<BaseSponge>();
    let (_, endo_r) = <Vesta as KimchiCurve<FULL_ROUNDS>>::endos();
    let lgr = verifier_index
        .srs()
        .get_lagrange_basis(verifier_index.domain);
    let ev = &proof.evals;
    let ev_public = ev
        .public
        .as_ref()
        .expect("chunked proof must carry public evaluations");

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
        "w_comm": proof.commitments.w_comm.iter().map(|c| commc(c, nc)).collect::<Vec<_>>(),
        "z_comm": commc(&proof.commitments.z_comm, nc),
        "t_comm": proof.commitments.t_comm.chunks.iter().map(pt).collect::<Vec<_>>(),
        "evals_public": pec(ev_public, nc),
        "evals_w": ev.w.iter().map(|e| pec(e, nc)).collect::<Vec<_>>(),
        "evals_z": pec(&ev.z, nc),
        "evals_s": ev.s.iter().map(|e| pec(e, nc)).collect::<Vec<_>>(),
        "evals_coefficients": ev.coefficients.iter().map(|e| pec(e, nc)).collect::<Vec<_>>(),
        "evals_generic_selector": pec(&ev.generic_selector, nc),
        "evals_poseidon_selector": pec(&ev.poseidon_selector, nc),
        "evals_complete_add_selector": pec(&ev.complete_add_selector, nc),
        "evals_mul_selector": pec(&ev.mul_selector, nc),
        "evals_emul_selector": pec(&ev.emul_selector, nc),
        "evals_endomul_scalar_selector": pec(&ev.endomul_scalar_selector, nc),
        "ft_eval1": fe(&proof.ft_eval1),
        "lr": proof.proof.lr.iter().map(|(l, r)| json!([pt(l), pt(r)])).collect::<Vec<_>>(),
        "delta": pt(&proof.proof.delta),
        "z1": fe(&proof.proof.z1),
        "z2": fe(&proof.proof.z2),
        "sg": pt(&proof.proof.sg),
    });

    let path = format!("{out_dir}/kimchi_proof_vesta_nc8.json");
    std::fs::write(&path, serde_json::to_string_pretty(&fixture).unwrap()).unwrap();
    println!(
        "kimchi proof (vesta, nc={nc}): n={} max_poly_size={} zk_rows={} t chunks={}, \
         production verify accepts; wrote {path}",
        verifier_index.domain.size(),
        verifier_index.max_poly_size,
        verifier_index.zk_rows,
        proof.commitments.t_comm.chunks.len()
    );
}
