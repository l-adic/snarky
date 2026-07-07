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

use ark_ec::AffineRepr;
use ark_ff::{Field, One, UniformRand, Zero};
use groupmap::GroupMap;
use kimchi::{
    circuits::{
        gate::{CircuitGate, GateType},
        polynomials::{endomul_scalar, generic::GenericGateSpec, poseidon as poseidon_gate},
        wires::Wire,
    },
    curve::KimchiCurve,
    proof::ProverProof,
    prover_index::testing::new_index_for_test,
    verifier::verify,
    verifier_index::VerifierIndex,
};
use mina_curves::pasta::{Fp, Pallas, Vesta, VestaParameters};
use mina_poseidon::{
    constants::PlonkSpongeConstantsKimchi as SC,
    pasta::{fp_kimchi, FULL_ROUNDS},
    sponge::{DefaultFqSponge, DefaultFrSponge},
};
use poly_commitment::ipa::endos;
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
    let params = fp_kimchi::static_params();

    // --- The gate table ---
    let mut gates: Vec<CircuitGate<Fp>> = vec![];
    // Row 0: the public row.
    gates.push(CircuitGate::create_generic_gadget(
        Wire::for_row(0),
        GenericGateSpec::Pub,
        None,
    ));
    // Row 1: w0 + w1 = w2; row 2: w0 * w1 = w2.
    gates.push(CircuitGate::create_generic_gadget(
        Wire::for_row(1),
        GenericGateSpec::Add { left_coeff: None, right_coeff: None, output_coeff: None },
        None,
    ));
    gates.push(CircuitGate::create_generic_gadget(
        Wire::for_row(2),
        GenericGateSpec::Mul { output_coeff: None, mul_coeff: None },
        None,
    ));
    // Wiring: public ↔ row 1 left input; row 1 output ↔ row 2 left input.
    gates[0].wires[0] = Wire { row: 1, col: 0 };
    gates[1].wires[0] = Wire { row: 0, col: 0 };
    gates[1].wires[2] = Wire { row: 2, col: 0 };
    gates[2].wires[0] = Wire { row: 1, col: 2 };
    // Rows 3..=14: the Poseidon gadget.
    let pos_row = gates.len();
    let (pos_gates, after_pos) = CircuitGate::<Fp>::create_poseidon_gadget(
        pos_row,
        [Wire::for_row(pos_row), Wire::for_row(pos_row + 11)],
        &params.round_constants,
    );
    gates.extend(pos_gates);
    // Row after the gadget's zero output row (create_poseidon_gadget returns the output
    // row itself): CompleteAdd on two random Pallas points.
    let add_row = after_pos + 1;
    gates.push(CircuitGate::new(GateType::CompleteAdd, Wire::for_row(add_row), vec![]));
    // Then 8 rows of EndoMulScalar (128 bits at 16 bits per row).
    let endo_row = add_row + 1;
    for r in 0..8 {
        gates.push(CircuitGate::new(
            GateType::EndoMulScalar,
            Wire::for_row(endo_row + r),
            vec![],
        ));
    }
    let n_gates = gates.len();

    // --- The witness ---
    let mut witness: [Vec<Fp>; COLUMNS] =
        std::array::from_fn(|_| vec![Fp::zero(); n_gates]);
    let pub0 = Fp::rand(rng);
    witness[0][0] = pub0;
    // Row 1: pub0 + b = o (left wired to the public row).
    let b = Fp::rand(rng);
    witness[0][1] = pub0;
    witness[1][1] = b;
    witness[2][1] = pub0 + b;
    // Row 2: (pub0 + b) * d = o (left wired to row 1's output).
    let d = Fp::rand(rng);
    witness[0][2] = pub0 + b;
    witness[1][2] = d;
    witness[2][2] = (pub0 + b) * d;
    // Poseidon block.
    poseidon_gate::generate_witness::<FULL_ROUNDS, Fp>(
        pos_row,
        params,
        &mut witness,
        [Fp::rand(rng), Fp::rand(rng), Fp::rand(rng)],
    );
    // CompleteAdd row: two distinct random Pallas points.
    {
        let p: Pallas = {
            let g = <Pallas as AffineRepr>::Group::rand(rng);
            g.into()
        };
        let q: Pallas = {
            let g = <Pallas as AffineRepr>::Group::rand(rng);
            g.into()
        };
        assert!(p.x != q.x, "unlucky sample: equal abscissae");
        let s = (q.y - p.y) / (q.x - p.x);
        let x3 = s.square() - p.x - q.x;
        let y3 = s * (p.x - x3) - p.y;
        let row = add_row;
        witness[0][row] = p.x;
        witness[1][row] = p.y;
        witness[2][row] = q.x;
        witness[3][row] = q.y;
        witness[4][row] = x3;
        witness[5][row] = y3;
        witness[6][row] = Fp::zero(); // inf
        witness[7][row] = Fp::zero(); // same_x
        witness[8][row] = s;
        witness[9][row] = Fp::zero(); // inf_z
        witness[10][row] = (q.x - p.x).inverse().unwrap(); // x21_inv
    }
    // EndoMulScalar block: build in a scratch table (the helper pushes), then copy.
    {
        let mut scratch: [Vec<Fp>; COLUMNS] = std::array::from_fn(|_| vec![]);
        let num_bits = 128;
        let x = {
            use ark_ff::{BigInteger, PrimeField};
            let bits: Vec<_> = ark_ff::BitIteratorLE::new(Fp::rand(rng).into_bigint())
                .take(num_bits)
                .collect();
            Fp::from_bigint(<Fp as PrimeField>::BigInt::from_bits_le(&bits)).unwrap()
        };
        let (_, endo_scalar_coeff) = endos::<Vesta>();
        let _ = endomul_scalar::gen_witness(&mut scratch, x, endo_scalar_coeff, num_bits);
        for col in 0..COLUMNS {
            for (r, v) in scratch[col].iter().enumerate() {
                witness[col][endo_row + r] = *v;
            }
        }
    }

    // --- The production index; kimchi's own row checker; prove and verify ---
    let index = new_index_for_test::<FULL_ROUNDS, Vesta>(gates, 1);
    index
        .verify(&witness, &[pub0])
        .expect("kimchi row checker rejected the witness");
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
            let wires: Vec<_> = (0..7).map(|c| json!([g.wires[c].col, g.wires[c].row])).collect();
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
        .map(|c| (0..n).map(|j| col_at(&ce.coefficients8[c].evals, 8, j)).collect())
        .collect();
    let sigma_cols: Vec<Vec<String>> = (0..7)
        .map(|c| (0..n).map(|j| col_at(&ce.permutation_coefficients8[c].evals, 8, j)).collect())
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
