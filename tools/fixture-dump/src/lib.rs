//! Shared fixture plumbing: the mixed-gate test circuit used by `index_dump` (the index
//! model fixture) and `linearization_dump` (the verifier scalar-side fixture) — one
//! construction, so both fixtures describe the same circuit family.

use ark_ec::AffineRepr;
use ark_ff::{Field, UniformRand, Zero};
use kimchi::circuits::{
    gate::{CircuitGate, GateType},
    polynomials::{endomul_scalar, generic::GenericGateSpec, poseidon as poseidon_gate},
    wires::Wire,
};
use mina_curves::pasta::{Fp, Pallas, Vesta};
use mina_poseidon::pasta::{fp_kimchi, FULL_ROUNDS};
use poly_commitment::ipa::endos;
use rand_chacha::ChaCha20Rng;

pub const COLUMNS: usize = 15;

/// The mixed-gate circuit with a real witness: a public row, two generic rows (add and
/// mul) wired to each other and to the public row, a full Poseidon gadget, a CompleteAdd
/// row on two random Pallas points, and an EndoMulScalar block. Returns the gates, the
/// witness table, and the public input value. Constraint satisfaction is the caller's
/// assertion (`index.verify`).
pub fn mixed_circuit(rng: &mut ChaCha20Rng) -> (Vec<CircuitGate<Fp>>, [Vec<Fp>; COLUMNS], Fp) {
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
        GenericGateSpec::Add {
            left_coeff: None,
            right_coeff: None,
            output_coeff: None,
        },
        None,
    ));
    gates.push(CircuitGate::create_generic_gadget(
        Wire::for_row(2),
        GenericGateSpec::Mul {
            output_coeff: None,
            mul_coeff: None,
        },
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
    gates.push(CircuitGate::new(
        GateType::CompleteAdd,
        Wire::for_row(add_row),
        vec![],
    ));
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
    let mut witness: [Vec<Fp>; COLUMNS] = std::array::from_fn(|_| vec![Fp::zero(); n_gates]);
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

    (gates, witness, pub0)
}
