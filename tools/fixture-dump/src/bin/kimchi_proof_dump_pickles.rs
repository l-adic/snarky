//! A pickles wrap proof, as produced by OCaml through the Rust prover, re-encoded as a
//! Lean kimchi-verifier fixture with its old accumulators (`prev_challenges`) — the
//! recursion path of `formal/kimchi/Kimchi/Verifier/Kimchi.lean` on a deployed
//! artifact (checked by `formal/kimchi/scripts/check_kimchi_verifier.lean`).
//!
//! Nothing here is generated: the proof and the verifier index are the side-loaded
//! fixtures the PureScript terminator verifies (`packages/pickles/test/fixtures/<chain>/
//! wrap<i>/{proof,vk}.serde.json`, upstream `ProverProof` / `VerifierIndex` serde), and
//! the public input and the accumulator list are what that terminator computes for them
//! (`lean_inputs.json`, written by `Test.Pickles.Sideload.LeanInputsSpec` from
//! `wrapPublicInputVP` and `wrapAccumulators`). This binary hydrates the index the way
//! kimchi-napi does (the SRS from the cached file, the endo, the linearization at the
//! basic gate set), checks the accumulator list equals the proof's own, runs the
//! production verifier — which must accept — and writes the one-chunk fixture format
//! with `prev_challenges` as `{comm, chals}` records and the key's
//! `prev_challenges_count`.
//!
//! A wrap proof's domain (`2^13`–`2^15` by `proofs_verified`, and `2^14` under the tests'
//! `override_wrap_domain`) is at most the `2^15` Tock SRS: production's sub-SRS
//! `chunk_size = 1` regime, which the Lean verifier takes as one chunk.

#![recursion_limit = "256"]

use ark_poly::EvaluationDomain;
use core::str::FromStr;
use groupmap::GroupMap;
use kimchi::{
    circuits::{
        constraints::FeatureFlags,
        lookup::lookups::{LookupFeatures, LookupPatterns},
        polynomials::permutation::{permutation_vanishing_polynomial, zk_w},
    },
    curve::KimchiCurve,
    linearization::expr_linearization,
    proof::ProverProof,
    verifier::verify,
    verifier_index::VerifierIndex,
};
use mina_curves::pasta::{Fq, Pallas, PallasParameters, Vesta};
use mina_poseidon::{
    constants::PlonkSpongeConstantsKimchi as SC,
    pasta::FULL_ROUNDS,
    sponge::{DefaultFqSponge, DefaultFrSponge},
};
use poly_commitment::{
    ipa::{endos, OpeningProof, SRS},
    SRS as _,
};
use serde_json::json;
use std::{fs::File, io::BufReader, sync::Arc};

type BaseSponge = DefaultFqSponge<PallasParameters, SC, FULL_ROUNDS>;
type ScalarSponge = DefaultFrSponge<Fq, SC, FULL_ROUNDS>;

fn fe<F: std::fmt::Display>(x: &F) -> String {
    format!("{}", x)
}

fn pt(g: &Pallas) -> serde_json::Value {
    use ark_ec::AffineRepr;
    assert!(!g.is_zero(), "fixture point unexpectedly at infinity");
    json!([fe(&g.x), fe(&g.y)])
}

/// A one-chunk `PolyComm` as a bare point.
fn comm1(c: &poly_commitment::commitment::PolyComm<Pallas>) -> serde_json::Value {
    assert_eq!(c.chunks.len(), 1, "expected a one-chunk commitment");
    pt(&c.chunks[0])
}

/// A `[zeta, zeta_omega]` evaluation pair, one chunk each.
fn pe(e: &kimchi::proof::PointEvaluations<Vec<Fq>>) -> serde_json::Value {
    assert_eq!(e.zeta.len(), 1, "expected one-chunk evaluations");
    assert_eq!(e.zeta_omega.len(), 1, "expected one-chunk evaluations");
    json!([fe(&e.zeta[0]), fe(&e.zeta_omega[0])])
}

/// A decimal field element, as the PureScript side writes them.
fn scalar(v: &serde_json::Value) -> Fq {
    Fq::from_str(v.as_str().expect("expected a decimal string")).expect("not a scalar")
}

/// A decimal base-field coordinate.
fn coord(v: &serde_json::Value) -> mina_curves::pasta::Fp {
    mina_curves::pasta::Fp::from_str(v.as_str().expect("expected a decimal string"))
        .expect("not a coordinate")
}

fn main() {
    let mut args = std::env::args().skip(1);
    let fixture_dir = args
        .next()
        .expect("usage: <fixture dir> <pallas srs file> <out dir>");
    let srs_path = args
        .next()
        .expect("usage: <fixture dir> <pallas srs file> <out dir>");
    let out_dir = args.next().unwrap_or_else(|| ".".to_string());

    // --- the SRS, from the cached file, as kimchi-napi reads it (the file may hold more
    // generators than the key's `max_poly_size`; `SRS::create` is prefix-consistent) ---
    let srs: SRS<Pallas> = {
        let file = File::open(&srs_path).expect("cannot open the SRS file");
        rmp_serde::from_read(BufReader::new(file)).expect("cannot deserialize the SRS")
    };

    // --- the verifier index: upstream serde, hydrated as kimchi-napi's `From` does ---
    let vk_json = std::fs::read_to_string(format!("{fixture_dir}/vk.serde.json"))
        .expect("cannot read vk.serde.json");
    let mut vi: VerifierIndex<FULL_ROUNDS, Pallas, SRS<Pallas>> =
        serde_json::from_str(&vk_json).expect("cannot deserialize the verifier index");
    assert!(
        vi.range_check0_comm.is_none()
            && vi.range_check1_comm.is_none()
            && vi.foreign_field_add_comm.is_none()
            && vi.foreign_field_mul_comm.is_none()
            && vi.xor_comm.is_none()
            && vi.rot_comm.is_none()
            && vi.lookup_index.is_none(),
        "the key uses optional gates or lookups: outside the Lean fragment"
    );
    assert!(
        vi.domain.size() <= vi.max_poly_size,
        "expected a one-chunk proof (domain at most the SRS)"
    );
    let feature_flags = FeatureFlags {
        range_check0: false,
        range_check1: false,
        foreign_field_add: false,
        foreign_field_mul: false,
        xor: false,
        rot: false,
        lookup_features: LookupFeatures {
            patterns: LookupPatterns {
                xor: false,
                lookup: false,
                range_check: false,
                foreign_field_mul: false,
            },
            joint_lookup_used: false,
            uses_runtime_tables: false,
        },
    };
    let (linearization, powers_of_alpha) = expr_linearization(Some(&feature_flags), true);
    vi.linearization = linearization;
    vi.powers_of_alpha = powers_of_alpha;
    vi.endo = endos::<Vesta>().0;
    vi.srs = Arc::new(srs);
    let zk_rows = vi.zk_rows;
    let _ = vi.w.set(zk_w(vi.domain, zk_rows));
    let _ = vi
        .permutation_vanishing_polynomial_m
        .set(permutation_vanishing_polynomial(vi.domain, zk_rows));

    // --- the proof: upstream serde ---
    let proof_json = std::fs::read_to_string(format!("{fixture_dir}/proof.serde.json"))
        .expect("cannot read proof.serde.json");
    let proof: ProverProof<Pallas, OpeningProof<Pallas, FULL_ROUNDS>, FULL_ROUNDS> =
        serde_json::from_str(&proof_json).expect("cannot deserialize the proof");

    // --- the terminator's inputs: the public input and the accumulator list ---
    let inputs: serde_json::Value = serde_json::from_str(
        &std::fs::read_to_string(format!("{fixture_dir}/lean_inputs.json"))
            .expect("cannot read lean_inputs.json (run Test.Pickles.Sideload.LeanInputsSpec)"),
    )
    .expect("cannot parse lean_inputs.json");
    let public_input: Vec<Fq> = inputs["publicInput"]
        .as_array()
        .expect("publicInput")
        .iter()
        .map(scalar)
        .collect();
    assert_eq!(
        public_input.len(),
        vi.public,
        "public input length vs the key's count"
    );
    let listed = inputs["prevChallenges"].as_array().expect("prevChallenges");
    assert_eq!(
        listed.len(),
        proof.prev_challenges.len(),
        "the terminator's accumulator list and the proof's own differ in length"
    );
    for (l, rc) in listed.iter().zip(proof.prev_challenges.iter()) {
        assert_eq!(rc.comm.chunks.len(), 1, "expected a one-chunk accumulator");
        assert_eq!(
            rc.comm.chunks[0].x,
            coord(&l["sgX"]),
            "accumulator sg.x differs"
        );
        assert_eq!(
            rc.comm.chunks[0].y,
            coord(&l["sgY"]),
            "accumulator sg.y differs"
        );
        let chals: Vec<Fq> = l["challenges"]
            .as_array()
            .expect("challenges")
            .iter()
            .map(scalar)
            .collect();
        assert_eq!(rc.chals, chals, "accumulator challenges differ");
    }
    assert_eq!(
        proof.prev_challenges.len(),
        vi.prev_challenges,
        "accumulator count vs the key's"
    );

    // --- the production verifier on the deployed artifact ---
    let group_map = <Pallas as poly_commitment::commitment::CommitmentCurve>::Map::setup();
    verify::<FULL_ROUNDS, Pallas, BaseSponge, ScalarSponge, _>(
        &group_map,
        &vi,
        &proof,
        &public_input,
    )
    .expect("production verifier rejected the pickles wrap proof");

    // --- the fixture, one-chunk format (the proof carries no evals.public) ---
    let digest = vi.digest::<BaseSponge>();
    let (_, endo_r) = Pallas::endos();
    let lgr = vi.srs().get_lagrange_basis(vi.domain);
    let ev = &proof.evals;
    assert!(
        ev.public.is_none(),
        "expected the deployed wire form without evals.public"
    );
    let prev_challenges: Vec<serde_json::Value> = proof
        .prev_challenges
        .iter()
        .map(|rc| {
            json!({
                "comm": rc.comm.chunks.iter().map(pt).collect::<Vec<_>>(),
                "chals": rc.chals.iter().map(fe).collect::<Vec<_>>(),
            })
        })
        .collect();

    let fixture = json!({
        "curve": "pallas",
        // --- verifier key ---
        "n": vi.domain.size().to_string(),
        "zk_rows": vi.zk_rows.to_string(),
        "max_poly_size": vi.max_poly_size.to_string(),
        "public_count": vi.public.to_string(),
        "prev_challenges_count": vi.prev_challenges.to_string(),
        "omega": fe(&vi.domain.group_gen),
        "shifts": vi.shift.iter().map(fe).collect::<Vec<_>>(),
        "endo": fe(&vi.endo),
        "endo_r": fe(endo_r),
        "digest": fe(&digest),
        // the SRS prefix the key was made against: the cached file may be longer, and the
        // verifier reads exactly `max_poly_size` generators
        "srs_g": vi.srs().g.iter().take(vi.max_poly_size).map(pt).collect::<Vec<_>>(),
        "srs_h": pt(&vi.srs().h),
        // the public prefix of the basis: all the verifier reads
        "lagrange_basis": lgr.iter().take(vi.public).map(comm1).collect::<Vec<_>>(),
        "sigma_comm": vi.sigma_comm.iter().map(comm1).collect::<Vec<_>>(),
        "coefficients_comm": vi.coefficients_comm.iter().map(comm1).collect::<Vec<_>>(),
        "generic_comm": comm1(&vi.generic_comm),
        "psm_comm": comm1(&vi.psm_comm),
        "complete_add_comm": comm1(&vi.complete_add_comm),
        "mul_comm": comm1(&vi.mul_comm),
        "emul_comm": comm1(&vi.emul_comm),
        "endomul_scalar_comm": comm1(&vi.endomul_scalar_comm),
        // --- public input ---
        "public": public_input.iter().map(fe).collect::<Vec<_>>(),
        // --- proof ---
        "prev_challenges": prev_challenges,
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

    let path = format!("{out_dir}/kimchi_proof_pallas_pickles.json");
    // Compact: the 2^15-generator SRS dominates the file, and pretty-printing doubles it.
    std::fs::write(&path, serde_json::to_string(&fixture).unwrap()).unwrap();

    println!(
        "pickles wrap proof: n={} accumulators={} public={}, production verify accepts; \
         wrote {path}",
        vi.domain.size(),
        proof.prev_challenges.len(),
        vi.public
    );
}
