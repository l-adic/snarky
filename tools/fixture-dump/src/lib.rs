//! Shared fixture plumbing: the mixed-gate test circuit used by `index_dump` (the index
//! model fixture) and `linearization_dump` (the verifier scalar-side fixture) — one
//! construction, so both fixtures describe the same circuit family.

use ark_ec::short_weierstrass::{Affine as SWAffine, Projective, SWCurveConfig};
use ark_ff::{PrimeField, UniformRand};
use kimchi::{
    circuits::{
        gate::{CircuitGate, GateType},
        polynomials::{endomul_scalar, generic::GenericGateSpec, poseidon as poseidon_gate},
        wires::Wire,
    },
    curve::KimchiCurve,
};
use mina_curves::pasta::{Fp, Fq, Pallas, PallasParameters, Vesta, VestaParameters};
use mina_poseidon::{
    pasta::{fp_kimchi, fq_kimchi, FULL_ROUNDS},
    poseidon::ArithmeticSpongeParams,
};
use poly_commitment::ipa::endos;
use rand_chacha::ChaCha20Rng;

pub const COLUMNS: usize = 15;

/// The mixed-gate circuit with a real witness: a public row, two generic rows (add and
/// mul) wired to each other and to the public row, a full Poseidon gadget, a CompleteAdd
/// row on two random points of the OTHER curve (whose base field is the circuit field),
/// and an EndoMulScalar block. Returns the gates, the witness table, and the public
/// input value. Constraint satisfaction is the caller's assertion (`index.verify`).
///
/// Generic over the circuit field so the same construction (and the same rng draw
/// order) yields both the Vesta-proof circuit over `Fp` and its Pallas twin over `Fq`;
/// use the `mixed_circuit` / `mixed_circuit_fq` wrappers.
pub fn mixed_circuit_over<F: PrimeField, OtherP: SWCurveConfig<BaseField = F>>(
    rng: &mut ChaCha20Rng,
    params: &'static ArithmeticSpongeParams<F, FULL_ROUNDS>,
    endo_scalar_coeff: F,
) -> (Vec<CircuitGate<F>>, [Vec<F>; COLUMNS], F) {
    // --- The gate table ---
    let mut gates: Vec<CircuitGate<F>> = vec![];
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
    let (pos_gates, after_pos) = CircuitGate::<F>::create_poseidon_gadget(
        pos_row,
        [Wire::for_row(pos_row), Wire::for_row(pos_row + 11)],
        &params.round_constants,
    );
    gates.extend(pos_gates);
    // Row after the gadget's zero output row (create_poseidon_gadget returns the output
    // row itself): CompleteAdd on two random other-curve points.
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
    let mut witness: [Vec<F>; COLUMNS] = std::array::from_fn(|_| vec![F::zero(); n_gates]);
    let pub0 = F::rand(rng);
    witness[0][0] = pub0;
    // Row 1: pub0 + b = o (left wired to the public row).
    let b = F::rand(rng);
    witness[0][1] = pub0;
    witness[1][1] = b;
    witness[2][1] = pub0 + b;
    // Row 2: (pub0 + b) * d = o (left wired to row 1's output).
    let d = F::rand(rng);
    witness[0][2] = pub0 + b;
    witness[1][2] = d;
    witness[2][2] = (pub0 + b) * d;
    // Poseidon block.
    poseidon_gate::generate_witness::<FULL_ROUNDS, F>(
        pos_row,
        params,
        &mut witness,
        [F::rand(rng), F::rand(rng), F::rand(rng)],
    );
    // CompleteAdd row: two distinct random points of the other curve.
    {
        let p: SWAffine<OtherP> = Projective::<OtherP>::rand(rng).into();
        let q: SWAffine<OtherP> = Projective::<OtherP>::rand(rng).into();
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
        witness[6][row] = F::zero(); // inf
        witness[7][row] = F::zero(); // same_x
        witness[8][row] = s;
        witness[9][row] = F::zero(); // inf_z
        witness[10][row] = (q.x - p.x).inverse().unwrap(); // x21_inv
    }
    // EndoMulScalar block: build in a scratch table (the helper pushes), then copy.
    {
        let mut scratch: [Vec<F>; COLUMNS] = std::array::from_fn(|_| vec![]);
        let num_bits = 128;
        let x = {
            use ark_ff::BigInteger;
            let bits: Vec<_> = ark_ff::BitIteratorLE::new(F::rand(rng).into_bigint())
                .take(num_bits)
                .collect();
            F::from_bigint(<F as PrimeField>::BigInt::from_bits_le(&bits)).unwrap()
        };
        let _ = endomul_scalar::gen_witness(&mut scratch, x, endo_scalar_coeff, num_bits);
        for col in 0..COLUMNS {
            for (r, v) in scratch[col].iter().enumerate() {
                witness[col][endo_row + r] = *v;
            }
        }
    }

    (gates, witness, pub0)
}

/// The Vesta-proof mixed circuit over `Fp` (CompleteAdd on Pallas points): the shape
/// every existing fixture records.
pub fn mixed_circuit(rng: &mut ChaCha20Rng) -> (Vec<CircuitGate<Fp>>, [Vec<Fp>; COLUMNS], Fp) {
    let (_, endo_scalar_coeff) = endos::<Vesta>();
    mixed_circuit_over::<Fp, PallasParameters>(rng, fp_kimchi::static_params(), endo_scalar_coeff)
}

/// The Pallas twin over `Fq` (CompleteAdd on Vesta points).
pub fn mixed_circuit_fq(rng: &mut ChaCha20Rng) -> (Vec<CircuitGate<Fq>>, [Vec<Fq>; COLUMNS], Fq) {
    let (_, endo_scalar_coeff) = endos::<Pallas>();
    mixed_circuit_over::<Fq, VestaParameters>(rng, fq_kimchi::static_params(), endo_scalar_coeff)
}

/// The mixed-gate prover index over a CUSTOM-SIZED SRS (rather than the 2^16
/// precomputed test SRS): the Lean executable verifier's IPA check does an SRS-sized
/// MSM per run and the kimchi-proof fixture carries the full generator vector, so
/// both stay CI-sized. `override_srs_size = None` gives the domain-sized SRS (one
/// chunk); `Some(size)` gives `max_poly_size = size`, i.e. `domain / size` chunks.
pub fn mixed_index_over<G>(
    gates: Vec<CircuitGate<G::ScalarField>>,
    override_srs_size: Option<usize>,
) -> kimchi::prover_index::ProverIndex<
    { mina_poseidon::pasta::FULL_ROUNDS },
    G,
    poly_commitment::ipa::SRS<G>,
>
where
    G: KimchiCurve<{ mina_poseidon::pasta::FULL_ROUNDS }>,
    G::BaseField: PrimeField,
    G::ScalarField: PrimeField,
{
    use poly_commitment::SRS as _;
    kimchi::prover_index::testing::new_index_for_test_with_lookups_and_custom_srs::<
        { mina_poseidon::pasta::FULL_ROUNDS },
        G,
        _,
        _,
    >(
        gates,
        1,
        0,
        vec![],
        None,
        false,
        override_srs_size,
        |d1, size| {
            let srs = poly_commitment::ipa::SRS::<G>::create(size);
            srs.get_lagrange_basis(d1);
            srs
        },
        false,
    )
}

/// The domain-sized (one-chunk) Vesta index — the shape shared by `linearization_dump`
/// and `kimchi_proof_dump`, so the two fixtures describe the same proof (same seed,
/// same SRS).
pub fn mixed_index(
    gates: Vec<kimchi::circuits::gate::CircuitGate<Fp>>,
) -> kimchi::prover_index::ProverIndex<
    { mina_poseidon::pasta::FULL_ROUNDS },
    Vesta,
    poly_commitment::ipa::SRS<Vesta>,
> {
    mixed_index_over::<Vesta>(gates, None)
}

/// A generic-only circuit over `Fp`: a public row and two wired generic rows (add, mul).
/// Generic gates use only the first four coefficient columns, so the other eleven are
/// zero polynomials and their verifier-key commitments are the group identity (the point
/// at infinity) — the case `kimchi_proof_dump_identity` records to exercise the verifier's
/// identity-commitment handling in the opening batch.
pub fn sparse_circuit(rng: &mut ChaCha20Rng) -> (Vec<CircuitGate<Fp>>, [Vec<Fp>; COLUMNS], Fp) {
    let mut gates: Vec<CircuitGate<Fp>> = vec![];
    gates.push(CircuitGate::create_generic_gadget(
        Wire::for_row(0),
        GenericGateSpec::Pub,
        None,
    ));
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
    // Wiring: public <-> row 1 left; row 1 output <-> row 2 left.
    gates[0].wires[0] = Wire { row: 1, col: 0 };
    gates[1].wires[0] = Wire { row: 0, col: 0 };
    gates[1].wires[2] = Wire { row: 2, col: 0 };
    gates[2].wires[0] = Wire { row: 1, col: 2 };
    let n_gates = gates.len();

    let mut witness: [Vec<Fp>; COLUMNS] = std::array::from_fn(|_| vec![Fp::from(0u64); n_gates]);
    let pub0 = Fp::rand(rng);
    witness[0][0] = pub0;
    let b = Fp::rand(rng);
    witness[0][1] = pub0;
    witness[1][1] = b;
    witness[2][1] = pub0 + b;
    let d = Fp::rand(rng);
    witness[0][2] = pub0 + b;
    witness[1][2] = d;
    witness[2][2] = (pub0 + b) * d;
    (gates, witness, pub0)
}
