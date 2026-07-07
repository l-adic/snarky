//! Kimchi permutation-argument data as a JSON fixture for the Lean formalization
//! (checked by `formal/scripts/check_perm_fixture.lean`).
//!
//! The circuit is deliberately degenerate — generic gates with no coefficients, so gate
//! constraints are vacuous — with a rich wiring: a 2-cycle, a 3-cycle, and a 4-cycle
//! across assorted columns and non-adjacent rows, everything else identity. Any witness
//! respecting the wiring is then valid; cells are seeded randoms with each cycle
//! overwritten by a shared value. What the fixture pins is the permutation argument
//! itself: the shifts (`Shifts::new`), the sigma columns, and the accumulator `z`
//! computed by the production `perm_aggreg`, all evaluated over the domain. The full
//! production pipeline is asserted by proving and verifying with the real prover.
//!
//! The Lean side re-checks, with its own transcribed formulas: the accumulator
//! recurrence at every unmasked row, the two boundary pins, the telescoped grand-product
//! equality, and the `CosetShifts` certificate for the dumped shift constants.

use ark_ff::{Field, UniformRand, Zero};
use ark_poly::Polynomial;
use groupmap::GroupMap;
use kimchi::{
    circuits::{
        gate::{CircuitGate, GateType},
        wires::Wire,
    },
    proof::ProverProof,
    prover_index::testing::new_index_for_test,
    verifier::verify,
    verifier_index::VerifierIndex,
};
use mina_curves::pasta::{Fp, Vesta, VestaParameters};
use mina_poseidon::{
    constants::PlonkSpongeConstantsKimchi as SC,
    pasta::{fp_kimchi, fq_kimchi, FULL_ROUNDS},
    sponge::{DefaultFqSponge, DefaultFrSponge},
};
use rand::SeedableRng;
use rand_chacha::ChaCha20Rng;
use serde_json::json;

type BaseSponge = DefaultFqSponge<VestaParameters, SC, FULL_ROUNDS>;
type ScalarSponge = DefaultFrSponge<Fp, SC, FULL_ROUNDS>;

const GATES: usize = 8;
const COLUMNS: usize = 15;
const PERMUTS: usize = 7;

fn fe<F: std::fmt::Display>(x: &F) -> String {
    format!("{}", x)
}

fn main() {
    let out_dir = std::env::args().nth(1).unwrap_or_else(|| ".".to_string());
    let rng = &mut ChaCha20Rng::from_seed([52u8; 32]);

    // Vacuous gates (generic, no coefficients) with identity wiring.
    let mut gates: Vec<CircuitGate<Fp>> = (0..GATES)
        .map(|row| CircuitGate::new(GateType::Generic, Wire::for_row(row), vec![]))
        .collect();

    // The wiring: cells listed cycle by cycle; each cell points to the next.
    let cycles: Vec<Vec<(usize, usize)>> = vec![
        vec![(0, 1), (5, 1)],                 // 2-cycle within a column
        vec![(1, 3), (3, 4), (6, 5)],         // 3-cycle across columns
        vec![(0, 0), (2, 6), (4, 2), (7, 0)], // 4-cycle touching the outer columns
    ];
    for cycle in &cycles {
        for (k, &(row, col)) in cycle.iter().enumerate() {
            let (nrow, ncol) = cycle[(k + 1) % cycle.len()];
            gates[row].wires[col] = Wire { row: nrow, col: ncol };
        }
    }

    // The production index (SRS, domain, shifts, sigma columns).
    let index = new_index_for_test::<FULL_ROUNDS, Vesta>(gates, 0);
    let n = index.cs.domain.d1.size as usize;
    let zk_rows = index.cs.zk_rows as usize;
    let omega = index.cs.domain.d1.group_gen;
    let shifts = index.cs.shift;

    // A witness respecting the wiring: seeded randoms, cycles sharing a value. Columns
    // beyond the permuted 7 stay zero. The prover receives the gate rows only (it pads
    // and zk-randomizes itself); perm_aggreg and the dump use the domain-padded form,
    // whose padding rows are identity-wired zeros.
    let mut witness: [Vec<Fp>; COLUMNS] = std::array::from_fn(|_| vec![Fp::zero(); GATES]);
    for col in witness.iter_mut().take(PERMUTS) {
        for cell in col.iter_mut().take(GATES) {
            *cell = Fp::rand(rng);
        }
    }
    for cycle in &cycles {
        let v = Fp::rand(rng);
        for &(row, col) in cycle {
            witness[col][row] = v;
        }
    }
    let witness_full: [Vec<Fp>; COLUMNS] = std::array::from_fn(|i| {
        let mut col = witness[i].clone();
        col.resize(n, Fp::zero());
        col
    });

    // The production accumulator at seeded challenges.
    let beta = Fp::rand(rng);
    let gamma = Fp::rand(rng);
    let z = index
        .perm_aggreg(&witness_full, &beta, &gamma, rng)
        .expect("perm_aggreg failed");

    // The full production pipeline accepts this circuit and witness.
    {
        let group_map = <Vesta as poly_commitment::commitment::CommitmentCurve>::Map::setup();
        let proof: ProverProof<Vesta, poly_commitment::ipa::OpeningProof<Vesta, FULL_ROUNDS>,
            FULL_ROUNDS> = ProverProof::create::<BaseSponge, ScalarSponge, _>(
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
            &[],
        )
        .expect("production verifier rejected the fixture circuit");
    }

    // Sigma columns over the domain, from the index's d8 evaluations (stride 8).
    let sigma8 = &index
        .column_evaluations
        .get()
        .permutation_coefficients8;
    let sigma_rows: Vec<Vec<String>> = (0..PERMUTS)
        .map(|i| (0..n).map(|j| fe(&sigma8[i].evals[8 * j])).collect())
        .collect();

    let pow = |k: usize| omega.pow([k as u64]);
    let fixture = json!({
        "curve": "vesta",
        "n": n.to_string(),
        "zk_rows": zk_rows.to_string(),
        "omega": fe(&omega),
        "beta": fe(&beta),
        "gamma": fe(&gamma),
        "shifts": shifts.iter().map(fe).collect::<Vec<_>>(),
        "witness": (0..PERMUTS)
            .map(|i| (0..n).map(|j| fe(&witness_full[i][j])).collect::<Vec<_>>())
            .collect::<Vec<_>>(),
        "sigma": sigma_rows,
        "z": (0..n).map(|j| fe(&z.evaluate(&pow(j)))).collect::<Vec<_>>(),
    });

    let path = format!("{out_dir}/perm_vesta.json");
    std::fs::write(&path, serde_json::to_string_pretty(&fixture).unwrap()).unwrap();
    println!("n={n} zk_rows={zk_rows}: production prove+verify accept; wrote {path}");
    let _ = fq_kimchi::static_params();
    let _ = fp_kimchi::static_params();
}
