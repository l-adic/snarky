//! Kimchi IPA opening proofs as wire-format JSON fixtures for the Lean formalization
//! (checked by `formal/scripts/check_ipa_fixture.lean`), over both Pasta curves.
//!
//! A fixture carries exactly what the wire protocol carries: the SRS, the per-polynomial
//! commitments, the evaluation points and claimed evaluations (uncombined), the combination
//! scalars `polyscale`/`evalscale`, and the opening proof (`lr`, `delta`, `z1`, `z2`, `sg`).
//! Nothing transcript-derived is recorded — the Lean side re-derives the `U` base and every
//! Fiat-Shamir challenge through its sponge layer (`formal/Kimchi/Sponge`) inside the
//! executable verifier (`formal/Kimchi/Verifier/Ipa.lean`).
//!
//! The proof is produced by the production `SRS::commit`/`SRS::open` and asserted accepted
//! by the production batched `SRS::verify`, following the harness of poly-commitment's
//! `tests/ipa_commitment.rs::test_opening_proof`.
//!
//! Deterministic (seeded ChaCha20), SRS size 4 (`k = 2` rounds). Four fixtures:
//! `ipa_opening_{vesta,pallas}.json` (1 polynomial × 1 point) and
//! `ipa_batch_{vesta,pallas}.json` (2 polynomials × 2 points).

use ark_ec::short_weierstrass::{Affine, SWCurveConfig};
use ark_ec::AffineRepr;
use ark_ff::{Field, PrimeField, UniformRand};
use ark_poly::{
    univariate::DensePolynomial, DenseUVPolynomial, Polynomial, Radix2EvaluationDomain,
};
use groupmap::GroupMap;
use mina_curves::pasta::{Pallas, PallasParameters, Vesta, VestaParameters};
use mina_poseidon::{
    constants::PlonkSpongeConstantsKimchi as SC, pasta::FULL_ROUNDS,
    poseidon::ArithmeticSpongeParams, sponge::DefaultFqSponge, FqSponge,
};
use poly_commitment::{
    commitment::{combined_inner_product, BatchEvaluationProof, CommitmentCurve, Evaluation},
    ipa::SRS,
    utils::DensePolynomialOrEvaluations,
    SRS as _,
};
use rand::SeedableRng;
use rand_chacha::ChaCha20Rng;
use serde_json::json;

const N: usize = 4; // SRS size
const K: usize = 2; // IPA rounds

fn fe<F: std::fmt::Display>(x: &F) -> String {
    format!("{}", x)
}

fn pt<P: SWCurveConfig>(g: &Affine<P>) -> serde_json::Value
where
    P::BaseField: std::fmt::Display,
{
    assert!(!g.is_zero(), "fixture point unexpectedly at infinity");
    json!([fe(&g.x), fe(&g.y)])
}

/// Produce one fixture: `n_polys` random degree-<4 polynomials opened at `n_points` random
/// points, with hiding commitments and random polyscale/evalscale.
#[allow(clippy::too_many_arguments)]
fn dump_fixture<P: SWCurveConfig>(
    srs: &SRS<Affine<P>>,
    params: &'static ArithmeticSpongeParams<P::BaseField, FULL_ROUNDS>,
    curve: &str,
    n_polys: usize,
    n_points: usize,
    seed: u8,
    out_path: &str,
) where
    P: Clone,
    P::BaseField: PrimeField,
    Affine<P>: CommitmentCurve
        + poly_commitment::commitment::EndoCurve
        + AffineRepr<ScalarField = P::ScalarField, BaseField = P::BaseField>,
    <P::BaseField as PrimeField>::BigInt: Into<<P::ScalarField as PrimeField>::BigInt>,
{
    type Sp<P> = DefaultFqSponge<P, SC, FULL_ROUNDS>;
    let rng = &mut ChaCha20Rng::from_seed([seed; 32]);

    // Polynomials, hiding commitments (one chunk each), evaluation points, eval matrix.
    let polys_dense: Vec<DensePolynomial<P::ScalarField>> = (0..n_polys)
        .map(|_| {
            let coeffs: Vec<P::ScalarField> = (0..N).map(|_| P::ScalarField::rand(rng)).collect();
            DensePolynomial::from_coefficients_slice(&coeffs)
        })
        .collect();
    let comms: Vec<_> = polys_dense.iter().map(|p| srs.commit(p, 1, rng)).collect();
    for c in &comms {
        assert_eq!(c.commitment.chunks.len(), 1);
    }
    let xs: Vec<P::ScalarField> = (0..n_points).map(|_| P::ScalarField::rand(rng)).collect();
    // es[i][j] = [ f_i(x_j) ]  (one chunk)
    let es: Vec<Vec<Vec<P::ScalarField>>> = polys_dense
        .iter()
        .map(|p| xs.iter().map(|x| vec![p.evaluate(x)]).collect())
        .collect();

    let polyscale = P::ScalarField::rand(rng);
    let evalscale = P::ScalarField::rand(rng);
    let cip = combined_inner_product(&polyscale, &evalscale, &es);

    // Produce the opening proof with the production prover.
    let group_map = <Affine<P> as CommitmentCurve>::Map::setup();
    let sponge = Sp::<P>::new(params);
    let to_open: Vec<(
        DensePolynomialOrEvaluations<P::ScalarField, Radix2EvaluationDomain<P::ScalarField>>,
        _,
    )> = polys_dense
        .iter()
        .zip(comms.iter())
        .map(|(p, c)| {
            (
                DensePolynomialOrEvaluations::DensePolynomial(p),
                c.blinders.clone(),
            )
        })
        .collect();
    let opening = srs.open(
        &group_map,
        &to_open,
        &xs,
        polyscale,
        evalscale,
        sponge.clone(),
        rng,
    );
    assert_eq!(opening.lr.len(), K);

    // The batched `SRS::verify` accepts the proof.
    {
        let evaluations: Vec<_> = comms
            .iter()
            .zip(es.iter())
            .map(|(cm, evals)| Evaluation {
                commitment: cm.commitment.clone(),
                evaluations: evals.clone(),
            })
            .collect();
        let mut batch = vec![BatchEvaluationProof {
            sponge: sponge.clone(),
            evaluation_points: xs.clone(),
            polyscale,
            evalscale,
            evaluations,
            opening: &opening,
            combined_inner_product: cip,
        }];
        assert!(
            srs.verify::<Sp<P>, _, FULL_ROUNDS>(&group_map, &mut batch, rng),
            "production SRS::verify rejected the fixture"
        );
    }

    let fixture = json!({
        "curve": curve,
        "k": K,
        "srs_g": srs.g.iter().map(pt).collect::<Vec<_>>(),
        "srs_h": pt(&srs.h),
        "commitments": comms.iter().map(|c| pt(&c.commitment.chunks[0])).collect::<Vec<_>>(),
        "xs": xs.iter().map(fe).collect::<Vec<_>>(),
        "evals": es.iter()
            .map(|per_point| per_point.iter().map(|ch| fe(&ch[0])).collect::<Vec<_>>())
            .collect::<Vec<_>>(),
        "polyscale": fe(&polyscale),
        "evalscale": fe(&evalscale),
        "lr": opening.lr.iter().map(|(l, r)| json!([pt(l), pt(r)])).collect::<Vec<_>>(),
        "delta": pt(&opening.delta),
        "z1": fe(&opening.z1),
        "z2": fe(&opening.z2),
        "sg": pt(&opening.sg),
    });

    std::fs::write(out_path, serde_json::to_string_pretty(&fixture).unwrap()).unwrap();
    println!(
        "{curve} {n_polys} poly(s) x {n_points} point(s): production verify accepts; wrote {out_path}"
    );
}

/// Chunked fixture: one polynomial of degree `< c*N` committed in `c` chunks, the
/// production `chunk_commitment(y)` combination at `y = x^N`, and an `nc = 1` opening of
/// the combined polynomial `sum_i y^i * chunk_i` at `x`. The Lean side recombines the raw
/// chunk points and chunk evaluations with its own formulas (`commit_combine` /
/// `eval_eq_sum_chunkPoly`), compares against the production combination, and runs the
/// executable verifier on the combined claim.
fn dump_chunked_fixture<P: SWCurveConfig>(
    srs: &SRS<Affine<P>>,
    params: &'static ArithmeticSpongeParams<P::BaseField, FULL_ROUNDS>,
    curve: &str,
    n_chunks: usize,
    seed: u8,
    out_path: &str,
) where
    P: Clone,
    P::BaseField: PrimeField,
    Affine<P>: CommitmentCurve
        + poly_commitment::commitment::EndoCurve
        + AffineRepr<ScalarField = P::ScalarField, BaseField = P::BaseField>,
    <P::BaseField as PrimeField>::BigInt: Into<<P::ScalarField as PrimeField>::BigInt>,
{
    type Sp<P> = DefaultFqSponge<P, SC, FULL_ROUNDS>;
    let rng = &mut ChaCha20Rng::from_seed([seed; 32]);

    // A degree-(c*N - 1) polynomial, committed in `c` chunks.
    let coeffs: Vec<P::ScalarField> =
        (0..n_chunks * N).map(|_| P::ScalarField::rand(rng)).collect();
    let p = DensePolynomial::from_coefficients_slice(&coeffs);
    let com = srs.commit(&p, n_chunks, rng);
    assert_eq!(com.commitment.chunks.len(), n_chunks);

    let x = P::ScalarField::rand(rng);
    let y = x.pow([N as u64]); // x^(srs size)

    // Per-chunk evaluations chunk_i(x) and the combined value v = p(x).
    let chunk_polys: Vec<DensePolynomial<P::ScalarField>> = (0..n_chunks)
        .map(|i| DensePolynomial::from_coefficients_slice(&coeffs[i * N..(i + 1) * N]))
        .collect();
    let chunk_evals: Vec<P::ScalarField> =
        chunk_polys.iter().map(|cp| cp.evaluate(&x)).collect();
    let v = p.evaluate(&x);
    // rust-side adjudication of the eval recombination
    let mut acc = P::ScalarField::from(0u64);
    for e in chunk_evals.iter().rev() {
        acc = acc * y + e;
    }
    assert_eq!(acc, v, "eval recombination mismatch");

    // The production combined commitment and the combined witness.
    let combined = com.commitment.chunk_commitment(y);
    assert_eq!(combined.chunks.len(), 1);
    let mut r_comb = P::ScalarField::from(0u64);
    for r in com.blinders.chunks.iter().rev() {
        r_comb = r_comb * y + r;
    }
    // Combined polynomial: coeff j = sum_i y^i * coeff (i*N + j).
    let p_comb = DensePolynomial::from_coefficients_vec(
        (0..N)
            .map(|j| {
                let mut a = P::ScalarField::from(0u64);
                for i in (0..n_chunks).rev() {
                    a = a * y + coeffs[i * N + j];
                }
                a
            })
            .collect(),
    );
    assert_eq!(p_comb.evaluate(&x), v, "combined polynomial evaluation mismatch");

    // nc = 1 opening of the combined polynomial at x, verified by production code.
    let polyscale = P::ScalarField::rand(rng);
    let evalscale = P::ScalarField::rand(rng);
    let es: Vec<Vec<Vec<P::ScalarField>>> = vec![vec![vec![v]]];
    let cip = combined_inner_product(&polyscale, &evalscale, &es);
    let group_map = <Affine<P> as CommitmentCurve>::Map::setup();
    let sponge = Sp::<P>::new(params);
    let blinder = poly_commitment::commitment::PolyComm { chunks: vec![r_comb] };
    let to_open: Vec<(
        DensePolynomialOrEvaluations<P::ScalarField, Radix2EvaluationDomain<P::ScalarField>>,
        _,
    )> = vec![(DensePolynomialOrEvaluations::DensePolynomial(&p_comb), blinder)];
    let opening = srs.open(
        &group_map,
        &to_open,
        &[x],
        polyscale,
        evalscale,
        sponge.clone(),
        rng,
    );
    {
        let evaluations = vec![Evaluation {
            commitment: combined.clone(),
            evaluations: vec![vec![v]],
        }];
        let mut batch = vec![BatchEvaluationProof {
            sponge: sponge.clone(),
            evaluation_points: vec![x],
            polyscale,
            evalscale,
            evaluations,
            opening: &opening,
            combined_inner_product: cip,
        }];
        assert!(
            srs.verify::<Sp<P>, _, FULL_ROUNDS>(&group_map, &mut batch, rng),
            "production SRS::verify rejected the chunked fixture"
        );
    }

    let fixture = json!({
        "curve": curve,
        "k": K,
        "srs_g": srs.g.iter().map(pt).collect::<Vec<_>>(),
        "srs_h": pt(&srs.h),
        // the standard nc = 1 opening view (combined commitment + combined value)
        "commitments": vec![pt(&combined.chunks[0])],
        "xs": vec![fe(&x)],
        "evals": vec![vec![fe(&v)]],
        "polyscale": fe(&polyscale),
        "evalscale": fe(&evalscale),
        "lr": opening.lr.iter().map(|(l, r)| json!([pt(l), pt(r)])).collect::<Vec<_>>(),
        "delta": pt(&opening.delta),
        "z1": fe(&opening.z1),
        "z2": fe(&opening.z2),
        "sg": pt(&opening.sg),
        // the chunk view the Lean side recombines itself
        "num_chunks": n_chunks,
        "chunk_commitments": com.commitment.chunks.iter().map(pt).collect::<Vec<_>>(),
        "chunk_evals": chunk_evals.iter().map(fe).collect::<Vec<_>>(),
    });

    std::fs::write(out_path, serde_json::to_string_pretty(&fixture).unwrap()).unwrap();
    println!(
        "{curve} chunked ({n_chunks} chunks): production verify accepts; wrote {out_path}"
    );
}

fn main() {
    let out_dir = std::env::args().nth(1).unwrap_or_else(|| ".".to_string());
    let srs_vesta = SRS::<Vesta>::create(N);
    let fq = mina_poseidon::pasta::fq_kimchi::static_params();
    dump_fixture::<VestaParameters>(
        &srs_vesta,
        fq,
        "vesta",
        1,
        1,
        42,
        &format!("{out_dir}/ipa_opening_vesta.json"),
    );
    dump_fixture::<VestaParameters>(
        &srs_vesta,
        fq,
        "vesta",
        2,
        2,
        43,
        &format!("{out_dir}/ipa_batch_vesta.json"),
    );
    let srs_pallas = SRS::<Pallas>::create(N);
    let fp = mina_poseidon::pasta::fp_kimchi::static_params();
    dump_fixture::<PallasParameters>(
        &srs_pallas,
        fp,
        "pallas",
        1,
        1,
        50,
        &format!("{out_dir}/ipa_opening_pallas.json"),
    );
    dump_fixture::<PallasParameters>(
        &srs_pallas,
        fp,
        "pallas",
        2,
        2,
        51,
        &format!("{out_dir}/ipa_batch_pallas.json"),
    );
    dump_chunked_fixture::<VestaParameters>(
        &srs_vesta,
        fq,
        "vesta",
        3,
        60,
        &format!("{out_dir}/ipa_chunked_vesta.json"),
    );
    dump_chunked_fixture::<PallasParameters>(
        &srs_pallas,
        fp,
        "pallas",
        3,
        61,
        &format!("{out_dir}/ipa_chunked_pallas.json"),
    );
}
