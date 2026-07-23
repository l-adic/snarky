//! A kimchi wire proof with two public inputs, as a JSON fixture for the Lean executable
//! verifier (`formal/scripts/check_kimchi_verifier.lean`).
//!
//! Same shape as `kimchi_proof_dump`'s `kimchi_proof_vesta.json` (one chunk, `nc = 1`,
//! no carried `evals_public`), over the two-public-input circuit
//! (`fixture_dump::two_public_circuit`) instead of the mixed circuit. `public_count = 2`
//! and `public` carries both inputs, so the verifier's public-commitment MSM and its
//! barycentric public-evaluation recomputation run over two elements — the multi-public
//! path every other fixture (all `public_count = 1`) leaves unexercised. Production
//! prove+verify is asserted at dump time.

use ark_poly::EvaluationDomain;
use fixture_dump::{two_public_circuit, two_public_index};
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
    let rng = &mut ChaCha20Rng::from_seed([83u8; 32]);

    let (gates, witness, pubs) = two_public_circuit(rng);
    let index = two_public_index(gates);
    index
        .verify(&witness, &pubs)
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
        &pubs,
    )
    .expect("production verifier rejected the fixture proof");
    assert_eq!(verifier_index.public, 2, "expected two public inputs");
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
        "public": pubs.iter().map(fe).collect::<Vec<_>>(),
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

    let path = format!("{out_dir}/kimchi_proof_vesta_2pub.json");
    std::fs::write(&path, serde_json::to_string_pretty(&fixture).unwrap()).unwrap();
    println!(
        "kimchi proof (2 public): n={} public={}, production verify accepts; wrote {path}",
        verifier_index.domain.size(),
        verifier_index.public,
    );
}
