//! A kimchi wire proof + verifier key over a circuit with LIVE `EndoMul` and
//! `VarBaseMul` rows, and an EMPTY public input — the two coverage gaps of the mixed
//! circuit (external-audit findings C-3 and V-1's mask; `docs/external-audit-report.md`).
//!
//! Every other committed proof fixture has `emul_selector ≡ 0` and `mul_selector ≡ 0`,
//! so the α-weighted EndoMul and VarBaseMul summands of the linearization's constant
//! term contribute nothing there: a verifier with those constraint lists mis-ordered
//! (the audit's V-1) still accepted every fixture. This proof's circuit is two EndoMul
//! rows (an 8-bit endo scalar), their shared accumulator row, and two
//! `VarBaseMul`/`Zero` pairs (a 10-bit scalar) — both selectors are live at ζ, so the
//! Lean verifier's acceptance pins the exact constraint order and the scalar-register
//! sign of both gates against production.
//!
//! `public_count = 0` besides: the public commitment degenerates to the all-ones
//! blinding mask (`nc` copies of `σ.h`) and the barycentric public evaluation to `0`,
//! the branch every other fixture leaves review-verified.
//!
//! Same wire-format conventions as `kimchi_proof_dump.rs` (`nc = 1`, no `evals_public`
//! recorded — the deployed representation).

use ark_ec::{AffineRepr, CurveGroup};
use ark_ff::{BitIteratorLE, PrimeField, UniformRand, Zero};
use ark_ec::AffineRepr as _;
use groupmap::GroupMap;
use kimchi::{
    circuits::{
        gate::{CircuitGate, GateType},
        polynomials::{endosclmul, varbasemul},
        wires::Wire,
    },
    curve::KimchiCurve,
    proof::ProverProof,
    verifier::verify,
    verifier_index::VerifierIndex,
};
use mina_curves::pasta::{Fp, Pallas, Vesta, VestaParameters};
use mina_poseidon::{
    constants::PlonkSpongeConstantsKimchi as SC,
    pasta::FULL_ROUNDS,
    sponge::{DefaultFqSponge, DefaultFrSponge},
};
use poly_commitment::{ipa::endos, SRS as _};
use rand::SeedableRng;
use rand_chacha::ChaCha20Rng;
use serde_json::json;

type BaseSponge = DefaultFqSponge<VestaParameters, SC, FULL_ROUNDS>;
type ScalarSponge = DefaultFrSponge<Fp, SC, FULL_ROUNDS>;

const COLUMNS: usize = 15;

fn fe<F: std::fmt::Display>(x: &F) -> String {
    format!("{}", x)
}

/// Unlike the mixed-circuit dumpers, this circuit's VK legitimately carries identity
/// commitments (the zero polynomials of the unused selector and coefficient columns),
/// encoded as the `(0, 0)` sentinel the Lean wire parser accepts (`parseSWPoint`).
fn pt(g: &Vesta) -> serde_json::Value {
    if g.is_zero() {
        json!(["0", "0"])
    } else {
        json!([fe(&g.x), fe(&g.y)])
    }
}

fn comm1(c: &poly_commitment::commitment::PolyComm<Vesta>) -> serde_json::Value {
    assert_eq!(c.chunks.len(), 1, "expected a one-chunk commitment");
    pt(&c.chunks[0])
}

fn pe(e: &kimchi::proof::PointEvaluations<Vec<Fp>>) -> serde_json::Value {
    assert_eq!(e.zeta.len(), 1, "expected one-chunk evaluations");
    assert_eq!(e.zeta_omega.len(), 1, "expected one-chunk evaluations");
    json!([fe(&e.zeta[0]), fe(&e.zeta_omega[0])])
}

/// The scalar-multiplication circuit: rows 0–1 `EndoMul` (8 bits, 4 per row), row 2 the
/// accumulator landing row (`Zero`), rows 3–6 two `VarBaseMul`/`Zero` pairs (10 bits,
/// 5 per pair). No public rows. Witnesses from production's own generators
/// (`endosclmul::gen_witness`, `varbasemul::witness`), exactly as kimchi's gate tests
/// build them.
fn emul_circuit(rng: &mut ChaCha20Rng) -> (Vec<CircuitGate<Fp>>, [Vec<Fp>; COLUMNS]) {
    let mut gates: Vec<CircuitGate<Fp>> = vec![];
    // EndoMul block: chunks rows 0..2, accumulator row 2.
    for row in 0..2 {
        gates.push(CircuitGate::new(GateType::EndoMul, Wire::for_row(row), vec![]));
    }
    gates.push(CircuitGate::new(GateType::Zero, Wire::for_row(2), vec![]));
    // VarBaseMul block: (VBSM, Zero) pairs at rows (3,4) and (5,6).
    for i in 0..2 {
        gates.push(CircuitGate::new(
            GateType::VarBaseMul,
            Wire::for_row(3 + 2 * i),
            vec![],
        ));
        gates.push(CircuitGate::new(
            GateType::Zero,
            Wire::for_row(3 + 2 * i + 1),
            vec![],
        ));
    }
    let n_rows = gates.len();
    let mut witness: [Vec<Fp>; COLUMNS] =
        std::array::from_fn(|_| vec![Fp::zero(); n_rows]);

    // EndoMul witness (the endomul.rs test harness at 8 bits).
    {
        let num_bits = 8;
        let (endo_q, _endo_r) = endos::<Pallas>();
        let bits_lsb: Vec<_> = BitIteratorLE::new(Fp::rand(rng).into_bigint())
            .take(num_bits)
            .collect();
        let bits_msb: Vec<_> = bits_lsb.iter().copied().rev().collect();
        let base = Pallas::generator();
        let acc0 = {
            let t = Pallas::new_unchecked(endo_q * base.x, base.y);
            let p = t + base;
            let acc: Pallas = (p + p).into();
            (acc.x, acc.y)
        };
        let _ = endosclmul::gen_witness(&mut witness, 0, endo_q, (base.x, base.y), &bits_msb, acc0);
    }
    // VarBaseMul witness (the varbasemul.rs test harness at 10 bits).
    {
        let num_bits = 10;
        let bits_lsb: Vec<_> = BitIteratorLE::new(Fp::rand(rng).into_bigint())
            .take(num_bits)
            .collect();
        let bits_msb: Vec<_> = bits_lsb.iter().copied().rev().collect();
        let base = Pallas::generator();
        let g = Pallas::generator().into_group();
        let acc = (g + g).into_affine();
        let _ = varbasemul::witness(&mut witness, 3, (base.x, base.y), &bits_msb, (acc.x, acc.y));
    }
    (gates, witness)
}

/// A domain-sized-SRS prover index with ZERO public inputs (`mixed_index_over` hardwires
/// one public row; this circuit has none).
fn index_pub0(
    gates: Vec<CircuitGate<Fp>>,
) -> kimchi::prover_index::ProverIndex<FULL_ROUNDS, Vesta, poly_commitment::ipa::SRS<Vesta>> {
    kimchi::prover_index::testing::new_index_for_test_with_lookups_and_custom_srs::<
        FULL_ROUNDS,
        Vesta,
        _,
        _,
    >(
        gates,
        0,
        0,
        vec![],
        None,
        false,
        None,
        |d1, size| {
            let srs = poly_commitment::ipa::SRS::<Vesta>::create(size);
            srs.get_lagrange_basis(d1);
            srs
        },
        false,
    )
}

fn main() {
    let out_dir = std::env::args().nth(1).unwrap_or_else(|| ".".to_string());
    let rng = &mut ChaCha20Rng::from_seed([83u8; 32]);

    let (gates, witness) = emul_circuit(rng);
    let index = index_pub0(gates);
    index
        .verify(&witness, &[])
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
        &[],
    )
    .expect("production verifier rejected the fixture proof");

    // The point of the fixture: both scalar-multiplication selectors are live at ζ.
    let ev = &proof.evals;
    assert!(
        !ev.emul_selector.zeta[0].is_zero(),
        "emul_selector unexpectedly zero at zeta"
    );
    assert!(
        !ev.mul_selector.zeta[0].is_zero(),
        "mul_selector unexpectedly zero at zeta"
    );

    let digest = verifier_index.digest::<BaseSponge>();
    let (_, endo_r) = Vesta::endos();
    let lgr = verifier_index
        .srs()
        .get_lagrange_basis(verifier_index.domain);
    use ark_poly::EvaluationDomain;

    let fixture = json!({
        "curve": "vesta",
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
        "public": [],
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

    let path = format!("{out_dir}/kimchi_proof_vesta_emul.json");
    std::fs::write(&path, serde_json::to_string_pretty(&fixture).unwrap()).unwrap();
    println!(
        "emul/vbm proof: n={} public=0, live emul+mul selectors, production verify \
         accepts; wrote {path}",
        verifier_index.domain.size()
    );
}
