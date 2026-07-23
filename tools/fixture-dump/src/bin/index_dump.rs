//! Mixed-gate kimchi circuits as JSON fixtures for the Lean index model
//! (checked by `formal/kimchi/scripts/check_index_fixture.lean` and
//! `formal/kimchi/scripts/check_vk_correspond.lean`).
//!
//! The circuit exercises every modeled gate type with a real witness: a public row, two
//! generic rows (add and mul) wired to each other and to the public row, a full Poseidon
//! gadget, a CompleteAdd row on two random other-curve points, and an EndoMulScalar block
//! — padded by the constraint system to the domain with zero rows. Constraints are checked
//! by kimchi's own row checker (`cs.verify`) and the full production prove+verify is
//! asserted at dump time (offline via the cached SRS).
//!
//! Three fixtures, each dumped by the same generic emitter over `mixed_index_over`:
//!
//! * `index_vesta.json` — the UNCHUNKED regression fixture (Vesta, `override_srs_size =
//!   None`, one chunk, `zk_rows = 3`, so the σ interior-mask range `[n − zk + 2, n − 1)`
//!   is EMPTY);
//! * `index_vesta_nc2.json` / `index_pallas_nc2.json` — the CHUNKED twins on BOTH curves
//!   (`override_srs_size = n / 2`, two chunks, `zk_rows = 5`, so the σ interior-mask range
//!   is NONEMPTY — rows 29, 30 at `n = 32`; a sign/off-by-one in the model's zeroing
//!   branch now fails a DIRECT row-level check).
//!
//! Dumped: the padded gate table exactly as the constraint system holds it (type,
//! coefficients, wire pointers per row), the domain and permutation constants, the
//! padded witness, the public input — and the production derived columns (selectors,
//! coefficients, sigmas) for the Lean side to compare its own derivations against. The
//! derived columns depend only on the gate structure and `zk_rows`, not the SRS, so the
//! chunked twins differ from the unchunked fixture only in `zk_rows` and the σ zeroing.

use ark_ff::{One, Zero};
use ark_poly::EvaluationDomain;
use fixture_dump::{mixed_circuit, mixed_circuit_fq, mixed_index_over};
use groupmap::GroupMap;
use kimchi::{
    circuits::gate::GateType, curve::KimchiCurve, proof::ProverProof, verifier::verify,
    verifier_index::VerifierIndex,
};
use mina_poseidon::{
    constants::PlonkSpongeConstantsKimchi as SC,
    pasta::FULL_ROUNDS,
    sponge::{DefaultFqSponge, DefaultFrSponge},
};
use rand::SeedableRng;
use rand_chacha::ChaCha20Rng;
use serde_json::json;

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

macro_rules! dump_index {
    ($modname:ident, $curve_str:literal, $G:ty, $GParams:ty, $F:ty, $circuit:path,
     $half:expr, $fname:literal) => {
        mod $modname {
            use super::*;

            type BaseSponge = DefaultFqSponge<$GParams, SC, FULL_ROUNDS>;
            type ScalarSponge = DefaultFrSponge<$F, SC, FULL_ROUNDS>;

            pub fn run(out_dir: &str) {
                // SAME seed as the existing regression fixture: the same circuit and
                // witness whichever chunking regime we re-index over.
                let rng = &mut ChaCha20Rng::from_seed([61u8; 32]);
                let (gates, witness, pub0) = $circuit(rng);
                let n_gates = gates.len();

                // Probe the chunk-free domain size, then (for the chunked twins) rebuild
                // over a half-size SRS. `override_srs_size = None` gives one chunk
                // (zk_rows = 3); `Some(n / 2)` gives two chunks (zk_rows = 5) at the same
                // domain size.
                let n_probe = mixed_index_over::<$G>(gates.clone(), None)
                    .cs
                    .domain
                    .d1
                    .size();
                let override_srs_size: Option<usize> =
                    if $half { Some(n_probe / 2) } else { None };
                let index = mixed_index_over::<$G>(gates, override_srs_size);
                assert_eq!(
                    index.cs.domain.d1.size(),
                    n_probe,
                    "domain grew under the chunked zk_rows; fixture story assumes a fixed n"
                );

                // kimchi's own row checker, then the full production prove + verify.
                index
                    .verify(&witness, &[pub0])
                    .expect("kimchi row checker rejected the witness");
                {
                    let group_map =
                        <$G as poly_commitment::commitment::CommitmentCurve>::Map::setup();
                    let proof: ProverProof<
                        $G,
                        poly_commitment::ipa::OpeningProof<$G, FULL_ROUNDS>,
                        FULL_ROUNDS,
                    > = ProverProof::create::<BaseSponge, ScalarSponge, _>(
                        &group_map,
                        witness.clone(),
                        &[],
                        &index,
                        rng,
                    )
                    .expect("prover failed");
                    let verifier_index: VerifierIndex<FULL_ROUNDS, $G, _> =
                        index.verifier_index();
                    verify::<FULL_ROUNDS, $G, BaseSponge, ScalarSponge, _>(
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
                            .map(|r| fe(witness[c].get(r).unwrap_or(&<$F>::zero())))
                            .collect()
                    })
                    .collect();

                // The padded gate table, exactly as the constraint system holds it.
                let gate_rows: Vec<_> = (0..n)
                    .map(|r| {
                        let g = &index.cs.gates[r];
                        let name = gate_type_name(g.typ).expect("unmodeled gate type in fixture");
                        let coeffs: Vec<String> = (0..15)
                            .map(|c| fe(g.coeffs.get(c).unwrap_or(&<$F>::zero())))
                            .collect();
                        let wires: Vec<_> = (0..7)
                            .map(|c| json!([g.wires[c].col, g.wires[c].row]))
                            .collect();
                        json!({ "typ": name, "coeffs": coeffs, "wires": wires })
                    })
                    .collect();

                // Production derived columns (d4/d8 evaluation strides).
                let ce = index.column_evaluations.get();
                let col_at = |evals: &[$F], stride: usize, j: usize| fe(&evals[stride * j]);
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
                    "curve": $curve_str,
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

                let path = format!("{out_dir}/{}", $fname);
                std::fs::write(&path, serde_json::to_string_pretty(&fixture).unwrap()).unwrap();
                println!(
                    "index ({}, {}): n={n} zk_rows={zk_rows} gates={n_gates}: cs.verify + \
                     production prove+verify accept; wrote {path}",
                    $curve_str,
                    if $half { "nc=2" } else { "nc=1" },
                );
                let _ = <$G as KimchiCurve<FULL_ROUNDS>>::sponge_params;
                let _ = <$F>::one();
            }
        }
    };
}

// The unchunked regression fixture (Vesta, one chunk, zk_rows = 3) — byte-identical to
// the historical `index_vesta.json`.
dump_index!(
    vesta,
    "vesta",
    mina_curves::pasta::Vesta,
    mina_curves::pasta::VestaParameters,
    mina_curves::pasta::Fp,
    mixed_circuit,
    false,
    "index_vesta.json"
);
// The chunked twins (two chunks, zk_rows = 5, nonempty σ interior mask) on both curves.
dump_index!(
    vesta_nc2,
    "vesta",
    mina_curves::pasta::Vesta,
    mina_curves::pasta::VestaParameters,
    mina_curves::pasta::Fp,
    mixed_circuit,
    true,
    "index_vesta_nc2.json"
);
dump_index!(
    pallas_nc2,
    "pallas",
    mina_curves::pasta::Pallas,
    mina_curves::pasta::PallasParameters,
    mina_curves::pasta::Fq,
    mixed_circuit_fq,
    true,
    "index_pallas_nc2.json"
);

fn main() {
    let out_dir = std::env::args().nth(1).unwrap_or_else(|| ".".to_string());
    vesta::run(&out_dir);
    vesta_nc2::run(&out_dir);
    pallas_nc2::run(&out_dir);
}
