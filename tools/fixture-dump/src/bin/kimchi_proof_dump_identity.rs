//! A kimchi wire proof whose verifier key has identity (point-at-infinity) coefficient
//! commitments, as a JSON fixture for the Lean executable verifier
//! (`formal/scripts/check_kimchi_verifier.lean`).
//!
//! Over the generic-only circuit (`fixture_dump::sparse_circuit`): it uses only the first
//! four of the fifteen coefficient columns, so the other eleven are zero polynomials and
//! their verifier-key commitments are the group identity. Points are emitted as `[x, y]`,
//! with the identity as `[0, 0]` — the `𝒪` sentinel the Lean `SWPoint` decoder accepts.
//! Same one-chunk (`nc = 1`) shape as `kimchi_proof_dump`'s `kimchi_proof_vesta.json`;
//! production prove+verify asserted.
//!
//! Scope: the identity commitments are consumed in the opening **batch**, so the fixture
//! exercises the verifier's identity handling on the **MSM path** (scalar-mul and add of
//! the `(0, 0)` sentinel). It does **not** exercise the Fq-sponge's absorption of an
//! identity point (audit finding M1): that path is reached only when a *sponge-absorbed*
//! commitment — a `w`/`z`/`t_comm` chunk or an IPA `L`/`R`/`δ` — is the identity, which an
//! honestly-produced proof never is. The VK commitments here reach the sponge only through
//! the precomputed `digest` (a wire input), not by individual absorption.

use ark_ec::AffineRepr;
use ark_poly::EvaluationDomain;
use fixture_dump::{mixed_index, sparse_circuit};
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

/// A point as `[x, y]`, with the identity emitted as the `[0, 0]` sentinel.
fn pt(g: &Vesta) -> serde_json::Value {
    if g.is_zero() {
        json!(["0", "0"])
    } else {
        json!([fe(&g.x), fe(&g.y)])
    }
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
    let rng = &mut ChaCha20Rng::from_seed([97u8; 32]);

    let (gates, witness, pub0) = sparse_circuit(rng);
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
    // The fixture is only meaningful if some commitment the verifier consumes really is
    // the identity. Scan the VK selectors, coefficients, sigmas, and the quotient chunks.
    let mut identity_points: Vec<String> = Vec::new();
    identity_points.extend(
        [
            ("generic_comm", &verifier_index.generic_comm),
            ("psm_comm", &verifier_index.psm_comm),
            ("complete_add_comm", &verifier_index.complete_add_comm),
            ("mul_comm", &verifier_index.mul_comm),
            ("emul_comm", &verifier_index.emul_comm),
            ("endomul_scalar_comm", &verifier_index.endomul_scalar_comm),
        ]
        .into_iter()
        .filter(|(_, c)| c.chunks[0].is_zero())
        .map(|(name, _)| name.to_string()),
    );
    identity_points.extend(
        verifier_index
            .coefficients_comm
            .iter()
            .enumerate()
            .filter(|(_, c)| c.chunks[0].is_zero())
            .map(|(i, _)| format!("coefficients_comm[{i}]")),
    );
    identity_points.extend(
        verifier_index
            .sigma_comm
            .iter()
            .enumerate()
            .filter(|(_, c)| c.chunks[0].is_zero())
            .map(|(i, _)| format!("sigma_comm[{i}]")),
    );
    identity_points.extend(
        proof
            .commitments
            .t_comm
            .chunks
            .iter()
            .enumerate()
            .filter(|(_, g)| g.is_zero())
            .map(|(i, _)| format!("t_comm[{i}]")),
    );
    assert!(
        !identity_points.is_empty(),
        "no commitment is the identity — the fixture would be vacuous"
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

    let path = format!("{out_dir}/kimchi_proof_vesta_identity.json");
    std::fs::write(&path, serde_json::to_string_pretty(&fixture).unwrap()).unwrap();
    println!(
        "kimchi proof (identity commitments: {}): n={}, production verify accepts; wrote {path}",
        identity_points.join(", "),
        verifier_index.domain.size(),
    );
}
