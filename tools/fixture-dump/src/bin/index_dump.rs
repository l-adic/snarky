//! A mixed-gate kimchi circuit as a JSON fixture for the Lean index model
//! (checked by `formal/scripts/check_index_fixture.lean`).
//!
//! The circuit exercises every modeled gate type with a real witness: a public row, two
//! generic rows (add and mul) wired to each other and to the public row, a full Poseidon
//! gadget, a CompleteAdd row on two random Pallas points, and an EndoMulScalar block —
//! padded by the constraint system to the domain with zero rows. Constraints are checked
//! by kimchi's own row checker (`cs.verify`) and the full production prove+verify is
//! asserted at dump time.
//!
//! Dumped: the padded gate table exactly as the constraint system holds it (type,
//! coefficients, wire pointers per row), the domain and permutation constants, the
//! padded witness, the public input — and the production derived columns (selectors,
//! coefficients, sigmas) for the Lean side to compare its own derivations against.

use ark_ff::{One, Zero};
use fixture_dump::mixed_circuit;
use groupmap::GroupMap;
use kimchi::{
    circuits::gate::GateType, curve::KimchiCurve, proof::ProverProof,
    prover_index::testing::new_index_for_test, verifier::verify, verifier_index::VerifierIndex,
};
use mina_curves::pasta::{Fp, Vesta, VestaParameters};
use mina_poseidon::{
    constants::PlonkSpongeConstantsKimchi as SC,
    pasta::FULL_ROUNDS,
    sponge::{DefaultFqSponge, DefaultFrSponge},
};
use rand::SeedableRng;
use rand_chacha::ChaCha20Rng;
use serde_json::json;

type BaseSponge = DefaultFqSponge<VestaParameters, SC, FULL_ROUNDS>;
type ScalarSponge = DefaultFrSponge<Fp, SC, FULL_ROUNDS>;

const COLUMNS: usize = 15;

fn fe<F: std::fmt::Display>(x: &F) -> String {
    format!("{}", x)
}

fn gate_type_name(t: GateType) -> Option<&'static str> {
    match t {
        GateType::Zero => Some("zero"),
        GateType::Generic => Some("generic"),
        GateType::Poseidon => Some("poseidon"),
        GateType::CompleteAdd => Some("completeAdd"),
        GateType::VarBaseMul => Some("varBaseMul"),
        GateType::EndoMul => Some("endoMul"),
        GateType::EndoMulScalar => Some("endoScalar"),
        _ => None,
    }
}

fn main() {
    let out_dir = std::env::args().nth(1).unwrap_or_else(|| ".".to_string());
    let rng = &mut ChaCha20Rng::from_seed([61u8; 32]);
    let (gates, witness, pub0) = mixed_circuit(rng);
    let n_gates = gates.len();

    // --- The production index; kimchi's own row checker; prove and verify ---
    let index = new_index_for_test::<FULL_ROUNDS, Vesta>(gates, 1);
    index
        .verify(&witness, &[pub0])
        .expect("kimchi row checker rejected the witness");
    {
        let group_map = <Vesta as poly_commitment::commitment::CommitmentCurve>::Map::setup();
        let proof: ProverProof<
            Vesta,
            poly_commitment::ipa::OpeningProof<Vesta, FULL_ROUNDS>,
            FULL_ROUNDS,
        > = ProverProof::create::<BaseSponge, ScalarSponge, _>(
            &group_map,
            witness.clone(),
            &[],
            &index,
            rng,
        )
        .expect("prover failed");
        let verifier_index: VerifierIndex<FULL_ROUNDS, Vesta, _> = index.verifier_index();
        verify::<FULL_ROUNDS, Vesta, BaseSponge, ScalarSponge, _>(
            &group_map,
            &verifier_index,
            &proof,
            &[pub0],
        )
        .expect("production verifier rejected the fixture circuit");
    }

    let n = index.cs.domain.d1.size as usize;
    let zk_rows = index.cs.zk_rows as usize;

    // Padded witness over the domain.
    let witness_full: Vec<Vec<String>> = (0..COLUMNS)
        .map(|c| {
            (0..n)
                .map(|r| fe(witness[c].get(r).unwrap_or(&Fp::zero())))
                .collect()
        })
        .collect();

    // The padded gate table, exactly as the constraint system holds it.
    let gate_rows: Vec<_> = (0..n)
        .map(|r| {
            let g = &index.cs.gates[r];
            let name = gate_type_name(g.typ).expect("unmodeled gate type in fixture");
            let coeffs: Vec<String> = (0..15)
                .map(|c| fe(g.coeffs.get(c).unwrap_or(&Fp::zero())))
                .collect();
            let wires: Vec<_> = (0..7)
                .map(|c| json!([g.wires[c].col, g.wires[c].row]))
                .collect();
            json!({ "typ": name, "coeffs": coeffs, "wires": wires })
        })
        .collect();

    // Production derived columns (d4/d8 evaluation strides).
    let ce = index.column_evaluations.get();
    let col_at = |evals: &[Fp], stride: usize, j: usize| fe(&evals[stride * j]);
    let selectors = json!({
        "generic": (0..n).map(|j| col_at(&ce.generic_selector4.evals, 4, j)).collect::<Vec<_>>(),
        "poseidon": (0..n).map(|j| col_at(&ce.poseidon_selector8.evals, 8, j)).collect::<Vec<_>>(),
        "completeAdd": (0..n).map(|j| col_at(&ce.complete_add_selector4.evals, 4, j)).collect::<Vec<_>>(),
        "varBaseMul": (0..n).map(|j| col_at(&ce.mul_selector8.evals, 8, j)).collect::<Vec<_>>(),
        "endoMul": (0..n).map(|j| col_at(&ce.emul_selector8.evals, 8, j)).collect::<Vec<_>>(),
        "endoScalar": (0..n).map(|j| col_at(&ce.endomul_scalar_selector8.evals, 8, j)).collect::<Vec<_>>(),
    });
    let coeff_cols: Vec<Vec<String>> = (0..15)
        .map(|c| {
            (0..n)
                .map(|j| col_at(&ce.coefficients8[c].evals, 8, j))
                .collect()
        })
        .collect();
    let sigma_cols: Vec<Vec<String>> = (0..7)
        .map(|c| {
            (0..n)
                .map(|j| col_at(&ce.permutation_coefficients8[c].evals, 8, j))
                .collect()
        })
        .collect();

    let fixture = json!({
        "curve": "vesta",
        "n": n.to_string(),
        "zk_rows": zk_rows.to_string(),
        "public_count": "1",
        "public": [fe(&pub0)],
        "omega": fe(&index.cs.domain.d1.group_gen),
        "endo_base": fe(&index.cs.endo),
        "shifts": index.cs.shift.iter().map(fe).collect::<Vec<_>>(),
        "gates": gate_rows,
        "witness": witness_full,
        "selectors": selectors,
        "coefficients": coeff_cols,
        "sigma": sigma_cols,
    });

    let path = format!("{out_dir}/index_vesta.json");
    std::fs::write(&path, serde_json::to_string_pretty(&fixture).unwrap()).unwrap();
    println!(
        "n={n} zk_rows={zk_rows} gates={n_gates}: cs.verify + production prove+verify \
         accept; wrote {path}",
    );
    let _ = <Vesta as KimchiCurve<FULL_ROUNDS>>::sponge_params;
    let _ = Fp::one();
}
