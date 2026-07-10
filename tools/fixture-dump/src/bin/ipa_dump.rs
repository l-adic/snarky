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
//! Deterministic (seeded ChaCha20), SRS size 4 (`k = 2` rounds). Two fixture kinds per
//! curve: combine-then-open (`dump_fixture` — mechanism (a), the per-polynomial
//! `chunk_commitment(x^n)` combination, single-point when chunked) and chunked-batch
//! (`dump_chunked_batch_fixture` — mechanism (b), multi-chunk `PolyComm`s consumed by
//! the batch path directly at consecutive polyscale powers, multi-point).

use ark_ec::short_weierstrass::{Affine, SWCurveConfig};
use ark_ec::{AffineRepr, CurveGroup};
use ark_ff::{Field, PrimeField, UniformRand, Zero};
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
    commitment::{
        combine_commitments, combined_inner_product, BatchEvaluationProof, CommitmentCurve,
        Evaluation,
    },
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

/// Produce one fixture: `n_polys` random polynomials of degree `< n_chunks * N`, each
/// committed in `n_chunks` chunks, opened at `n_points` random points. Chunking is the
/// general case — `n_chunks = 1` is the one-element instance of the same schema. For
/// `n_chunks > 1` the fixture follows the verifier's combine-then-open order
/// (mechanism (a)): the chunk commitments are combined with `y = x^N` by the production
/// `chunk_commitment`, and the combined polynomial is opened — which is anchored to THE
/// evaluation point, so chunked fixtures are single-point (multi-point chunked batches
/// are the polyscale folding, a separate mechanism).
#[allow(clippy::too_many_arguments)]
fn dump_fixture<P: SWCurveConfig>(
    srs: &SRS<Affine<P>>,
    params: &'static ArithmeticSpongeParams<P::BaseField, FULL_ROUNDS>,
    curve: &str,
    n_polys: usize,
    n_points: usize,
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
    assert!(
        n_chunks == 1 || n_points == 1,
        "chunked fixtures are single-point (combine-then-open is anchored to the point)"
    );
    type Sp<P> = DefaultFqSponge<P, SC, FULL_ROUNDS>;
    let rng = &mut ChaCha20Rng::from_seed([seed; 32]);

    // Polynomials of degree < n_chunks * N, committed in n_chunks chunks.
    let coeffs_all: Vec<Vec<P::ScalarField>> = (0..n_polys)
        .map(|_| {
            (0..n_chunks * N)
                .map(|_| P::ScalarField::rand(rng))
                .collect()
        })
        .collect();
    let polys_dense: Vec<DensePolynomial<P::ScalarField>> = coeffs_all
        .iter()
        .map(|cs| DensePolynomial::from_coefficients_slice(cs))
        .collect();
    let comms: Vec<_> = polys_dense
        .iter()
        .map(|p| srs.commit(p, n_chunks, rng))
        .collect();
    for c in &comms {
        assert_eq!(c.commitment.chunks.len(), n_chunks);
    }
    let xs: Vec<P::ScalarField> = (0..n_points).map(|_| P::ScalarField::rand(rng)).collect();
    let y = xs[0].pow([N as u64]); // x^(srs size); irrelevant at n_chunks = 1

    // Per-poly: production combined commitment, combined blinder, combined polynomial
    // (all identities at n_chunks = 1).
    let combined: Vec<_> = comms
        .iter()
        .map(|c| c.commitment.chunk_commitment(y))
        .collect();
    let r_combs: Vec<P::ScalarField> = comms
        .iter()
        .map(|c| {
            let mut r = P::ScalarField::from(0u64);
            for b in c.blinders.chunks.iter().rev() {
                r = r * y + b;
            }
            r
        })
        .collect();
    let p_combs: Vec<DensePolynomial<P::ScalarField>> = coeffs_all
        .iter()
        .map(|cs| {
            DensePolynomial::from_coefficients_vec(
                (0..N)
                    .map(|j| {
                        let mut a = P::ScalarField::from(0u64);
                        for i in (0..n_chunks).rev() {
                            a = a * y + cs[i * N + j];
                        }
                        a
                    })
                    .collect(),
            )
        })
        .collect();

    // Chunk evaluations chunk_i(x_j) per poly per point, and the combined values;
    // rust-side adjudication of the eval recombination per point.
    let chunk_evals: Vec<Vec<Vec<P::ScalarField>>> = coeffs_all
        .iter()
        .map(|cs| {
            xs.iter()
                .map(|x| {
                    (0..n_chunks)
                        .map(|i| {
                            DensePolynomial::from_coefficients_slice(&cs[i * N..(i + 1) * N])
                                .evaluate(x)
                        })
                        .collect()
                })
                .collect()
        })
        .collect();
    let vs: Vec<Vec<P::ScalarField>> = p_combs
        .iter()
        .map(|p| xs.iter().map(|x| p.evaluate(x)).collect())
        .collect();
    for (i, per_point) in chunk_evals.iter().enumerate() {
        for (j, ch) in per_point.iter().enumerate() {
            let yj = xs[j].pow([N as u64]);
            let mut acc = P::ScalarField::from(0u64);
            for e in ch.iter().rev() {
                acc = acc * yj + e;
            }
            // at n_chunks > 1 we have n_points = 1, so yj = y and this is the
            // combined value; at n_chunks = 1 it is trivially the value itself
            assert_eq!(acc, vs[i][j], "eval recombination mismatch");
        }
    }

    // Open the combined polynomials, verified by production code.
    let polyscale = P::ScalarField::rand(rng);
    let evalscale = P::ScalarField::rand(rng);
    let es: Vec<Vec<Vec<P::ScalarField>>> = vs
        .iter()
        .map(|per_point| per_point.iter().map(|v| vec![*v]).collect())
        .collect();
    let cip = combined_inner_product(&polyscale, &evalscale, &es);
    let group_map = <Affine<P> as CommitmentCurve>::Map::setup();
    let sponge = Sp::<P>::new(params);
    let blinders: Vec<_> = r_combs
        .iter()
        .map(|r| poly_commitment::commitment::PolyComm { chunks: vec![*r] })
        .collect();
    let to_open: Vec<(
        DensePolynomialOrEvaluations<P::ScalarField, Radix2EvaluationDomain<P::ScalarField>>,
        _,
    )> = p_combs
        .iter()
        .zip(blinders.iter())
        .map(|(p, b)| (DensePolynomialOrEvaluations::DensePolynomial(p), b.clone()))
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
    {
        let evaluations: Vec<_> = combined
            .iter()
            .zip(es.iter())
            .map(|(cm, evals)| Evaluation {
                commitment: cm.clone(),
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
        "num_chunks": n_chunks,
        "srs_g": srs.g.iter().map(pt).collect::<Vec<_>>(),
        "srs_h": pt(&srs.h),
        // per poly: the chunk points (the wire object) and the production combination
        "commitments": comms.iter()
            .map(|c| c.commitment.chunks.iter().map(pt).collect::<Vec<_>>())
            .collect::<Vec<_>>(),
        "combined_commitments": combined.iter()
            .map(|c| pt(&c.chunks[0]))
            .collect::<Vec<_>>(),
        "xs": xs.iter().map(fe).collect::<Vec<_>>(),
        // per poly per point: the chunk evaluations and the combined value
        "chunk_evals": chunk_evals.iter()
            .map(|pp| pp.iter()
                .map(|ch| ch.iter().map(fe).collect::<Vec<_>>())
                .collect::<Vec<_>>())
            .collect::<Vec<_>>(),
        "evals": vs.iter()
            .map(|per_point| per_point.iter().map(fe).collect::<Vec<_>>())
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
        "{curve} {n_polys} poly(s) x {n_points} point(s) x {n_chunks} chunk(s): \
production verify accepts; wrote {out_path}"
    );
}

/// Produce one chunked-batch fixture (mechanism (b)): one random polynomial per entry
/// of `n_chunks`, polynomial `i` of degree `< n_chunks[i] * N` committed as an
/// `n_chunks[i]`-chunk `PolyComm` (ragged counts allowed — the deployed batch mixes
/// widths), opened at `n_points` points through the production batch path directly —
/// `SRS::open` folds the chunk segments at consecutive polyscale powers
/// (polynomial-outer, chunk-inner, no reset at a polynomial boundary) and `SRS::verify`
/// consumes the multi-chunk commitments as-is. No per-polynomial combination exists on
/// this path; the fixture records the production flat combination targets —
/// `combine_commitments` at `rand_base = 1` and `combined_inner_product` — for the Lean
/// side to adjudicate its chunked combiners against.
fn dump_chunked_batch_fixture<P: SWCurveConfig>(
    srs: &SRS<Affine<P>>,
    params: &'static ArithmeticSpongeParams<P::BaseField, FULL_ROUNDS>,
    curve: &str,
    n_chunks: &[usize],
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

    // Polynomial i of degree < n_chunks[i] * N, committed as an n_chunks[i]-chunk
    // PolyComm.
    let coeffs_all: Vec<Vec<P::ScalarField>> = n_chunks
        .iter()
        .map(|&nc| (0..nc * N).map(|_| P::ScalarField::rand(rng)).collect())
        .collect();
    let polys_dense: Vec<DensePolynomial<P::ScalarField>> = coeffs_all
        .iter()
        .map(|cs| DensePolynomial::from_coefficients_slice(cs))
        .collect();
    let comms: Vec<_> = polys_dense
        .iter()
        .zip(n_chunks.iter())
        .map(|(p, &nc)| srs.commit(p, nc, rng))
        .collect();
    for (c, &nc) in comms.iter().zip(n_chunks.iter()) {
        assert_eq!(c.commitment.chunks.len(), nc);
    }
    let xs: Vec<P::ScalarField> = (0..n_points).map(|_| P::ScalarField::rand(rng)).collect();

    // Chunk evaluations chunk_i(x_j), [poly][point][chunk] — exactly the layout
    // combined_inner_product consumes (point rows, segment columns).
    let chunk_evals: Vec<Vec<Vec<P::ScalarField>>> = coeffs_all
        .iter()
        .zip(n_chunks.iter())
        .map(|(cs, &nc)| {
            xs.iter()
                .map(|x| {
                    (0..nc)
                        .map(|i| {
                            DensePolynomial::from_coefficients_slice(&cs[i * N..(i + 1) * N])
                                .evaluate(x)
                        })
                        .collect()
                })
                .collect()
        })
        .collect();

    let polyscale = P::ScalarField::rand(rng);
    let evalscale = P::ScalarField::rand(rng);
    let cip = combined_inner_product(&polyscale, &evalscale, &chunk_evals);

    // Open the raw chunked polynomials — production folds the segment stream itself.
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

    let evaluations: Vec<_> = comms
        .iter()
        .zip(chunk_evals.iter())
        .map(|(c, evals)| Evaluation {
            commitment: c.commitment.clone(),
            evaluations: evals.clone(),
        })
        .collect();

    // The production flat combination of the segment stream, at rand_base = 1.
    let batch_combined = {
        let mut scalars = vec![];
        let mut points = vec![];
        combine_commitments(
            &evaluations,
            &mut scalars,
            &mut points,
            polyscale,
            P::ScalarField::from(1u64),
        );
        let mut acc = <Affine<P> as AffineRepr>::Group::zero();
        for (s, p) in scalars.iter().zip(points.iter()) {
            acc += *p * *s;
        }
        acc.into_affine()
    };

    {
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
            "production SRS::verify rejected the chunked-batch fixture"
        );
    }

    let fixture = json!({
        "curve": curve,
        "k": K,
        "num_chunks": n_chunks,
        "srs_g": srs.g.iter().map(pt).collect::<Vec<_>>(),
        "srs_h": pt(&srs.h),
        // per poly: the chunk points (the wire object, uncombined)
        "commitments": comms.iter()
            .map(|c| c.commitment.chunks.iter().map(pt).collect::<Vec<_>>())
            .collect::<Vec<_>>(),
        "xs": xs.iter().map(fe).collect::<Vec<_>>(),
        // per poly per point: the chunk evaluations
        "chunk_evals": chunk_evals.iter()
            .map(|pp| pp.iter()
                .map(|ch| ch.iter().map(fe).collect::<Vec<_>>())
                .collect::<Vec<_>>())
            .collect::<Vec<_>>(),
        "polyscale": fe(&polyscale),
        "evalscale": fe(&evalscale),
        // the production flat combination targets
        "combined_inner_product": fe(&cip),
        "batch_combined_commitment": pt(&batch_combined),
        "lr": opening.lr.iter().map(|(l, r)| json!([pt(l), pt(r)])).collect::<Vec<_>>(),
        "delta": pt(&opening.delta),
        "z1": fe(&opening.z1),
        "z2": fe(&opening.z2),
        "sg": pt(&opening.sg),
    });

    std::fs::write(out_path, serde_json::to_string_pretty(&fixture).unwrap()).unwrap();
    println!(
        "{curve} chunked batch, {} poly(s) x {n_points} point(s), chunks {n_chunks:?}: \
production verify accepts; wrote {out_path}",
        n_chunks.len()
    );
}

fn main() {
    let out_dir = std::env::args().nth(1).unwrap_or_else(|| ".".to_string());
    let srs_vesta = SRS::<Vesta>::create(N);
    let fq = mina_poseidon::pasta::fq_kimchi::static_params();
    let srs_pallas = SRS::<Pallas>::create(N);
    let fp = mina_poseidon::pasta::fp_kimchi::static_params();
    // breadth over (n_polys, n_points, n_chunks): 1x1x1, 2x2x1, 1x1x2, 1x1x3
    for (name, np, nx, nc, sv, sp) in [
        ("opening", 1, 1, 1, 42, 50),
        ("batch", 2, 2, 1, 43, 51),
        ("chunked2", 1, 1, 2, 60, 61),
        ("chunked3", 1, 1, 3, 62, 63),
    ] {
        dump_fixture::<VestaParameters>(
            &srs_vesta,
            fq,
            "vesta",
            np,
            nx,
            nc,
            sv,
            &format!("{out_dir}/ipa_{name}_vesta.json"),
        );
        dump_fixture::<PallasParameters>(
            &srs_pallas,
            fp,
            "pallas",
            np,
            nx,
            nc,
            sp,
            &format!("{out_dir}/ipa_{name}_pallas.json"),
        );
    }
    // mechanism (b): multi-chunk PolyComms through the batch path, multi-point —
    // uniform chunk counts, then ragged (the prefix-sum segment offsets)
    for (name, ncs, sv, sp) in [
        ("chunked_batch", &[2usize, 2][..], 64, 65),
        ("chunked_ragged", &[1usize, 3][..], 66, 67),
    ] {
        dump_chunked_batch_fixture::<VestaParameters>(
            &srs_vesta,
            fq,
            "vesta",
            ncs,
            2,
            sv,
            &format!("{out_dir}/ipa_{name}_vesta.json"),
        );
        dump_chunked_batch_fixture::<PallasParameters>(
            &srs_pallas,
            fp,
            "pallas",
            ncs,
            2,
            sp,
            &format!("{out_dir}/ipa_{name}_pallas.json"),
        );
    }
}
