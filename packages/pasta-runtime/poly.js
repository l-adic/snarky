// Pure-JS polynomial / domain helpers used by Pickles when consuming
// kimchi proofs. These mirror Rust functions in `mina/.../proof-systems/`:
//
//   * `domain_generator(log2)`                      — Radix2EvaluationDomain::group_gen
//   * `eval_vanishes_on_last_n_rows(log2, n, pt)`   — kimchi/circuits/polynomials/permutation.rs
//   * `permutation_vanishing_polynomial(log2, zk, pt)` — same module
//   * `unnormalized_lagrange_basis(log2, zk, off, pt)` — kimchi/circuits/expr.rs:132
//   * `vanishes_on_zk_and_previous_rows(log2, zk, pt)` — eval_vanishes_on_last_n_rows(log2, zk+1, pt)
//   * `b_poly(chals, x)`                            — poly-commitment/commitment.rs:416
//   * `compute_b0(chals, zeta, zetaOmega, scale)`   — b_poly(chals, zeta) + scale * b_poly(chals, zetaOmega)
//
// All inputs/outputs are bigints in the appropriate prime field. The field
// parameter `F` is one of the `createField`-returned objects from
// `./PastaField.js` (Fp or Fq).
//
// 2-adic root convention:
//   F has a 2-adic root of unity of order 2^TWOADICITY (= 2^32 for both
//   Pasta primes). For domain size n = 2^log2, the n-th root of unity is
//   the 2-adic root squared (TWOADICITY - log2) times.

import { Fp, Fq, TWOADIC_ROOT_FP, TWOADIC_ROOT_FQ, TWOADICITY, mod } from './PastaField.js';

const TWOADICITY_NUM = Number(TWOADICITY);

/**
 * Pick the right Pasta field by its modulus (for callers that want a
 * generic helper without re-importing Fp/Fq).
 */
export function fieldOf(modulus) {
  if (modulus === Fp.modulus) return Fp;
  if (modulus === Fq.modulus) return Fq;
  throw new Error(`fieldOf: not a Pasta field modulus`);
}

/**
 * 2^log2-th primitive root of unity in field F.
 *
 * For Arkworks's Radix2EvaluationDomain, `group_gen` = 2-adic root squared
 * `(TWO_ADICITY - log2)` times. Both Pasta primes have TWO_ADICITY = 32.
 */
export function domainGenerator(F, log2) {
  if (log2 < 0 || log2 > TWOADICITY_NUM) {
    throw new Error(`domainGenerator: log2 ${log2} out of [0, ${TWOADICITY_NUM}]`);
  }
  const root = F.modulus === Fp.modulus ? TWOADIC_ROOT_FP : TWOADIC_ROOT_FQ;
  // Apply (TWOADICITY - log2) doublings (square = pow 2).
  let g = mod(root, F.modulus);
  for (let i = 0; i < TWOADICITY_NUM - log2; i++) g = F.square(g);
  return g;
}

/**
 * Evaluates ∏_{j=0}^{n-1} (pt - ω^(domainSize - n + j)) at `pt`.
 *
 * Direct port of `eval_vanishes_on_last_n_rows` in
 * `kimchi/src/circuits/polynomials/permutation.rs:68`.
 */
export function evalVanishesOnLastNRows(F, log2, n, pt) {
  if (n === 0n || n === 0) return 1n;
  const nBig = typeof n === 'bigint' ? n : BigInt(n);
  const size = 1n << BigInt(log2);
  const omega = domainGenerator(F, log2);
  let term = F.power(omega, size - nBig);
  let acc = F.sub(pt, term);
  for (let i = 0n; i < nBig - 1n; i++) {
    term = F.mul(term, omega);
    acc = F.mul(acc, F.sub(pt, term));
  }
  return acc;
}

/**
 * Permutation vanishing polynomial evaluated at `pt`:
 *   (pt - ω^(n - zk_rows)) * (pt - ω^(n - zk_rows + 1)) * (pt - ω^(n - 1))
 *
 * Mirrors `eval_permutation_vanishing_polynomial` in kimchi (and the
 * `pallas_permutation_vanishing_polynomial` napi binding in snarky-crypto,
 * which calls `eval_vanishes_on_last_n_rows(log2, zk_rows, pt)` — *not*
 * `zk_rows + 1`).
 */
export function permutationVanishingPolynomial(F, log2, zkRows, pt) {
  return evalVanishesOnLastNRows(F, log2, BigInt(zkRows), pt);
}

/**
 * `VanishesOnZeroKnowledgeAndPreviousRows` term used in the linearization.
 * Equals `eval_vanishes_on_last_n_rows(log2, zk_rows + 1, pt)` — note the
 * +1, in contrast to `permutationVanishingPolynomial`.
 */
export function vanishesOnZkAndPreviousRows(F, log2, zkRows, pt) {
  return evalVanishesOnLastNRows(F, log2, BigInt(zkRows) + 1n, pt);
}

/**
 * Unnormalized i-th Lagrange basis polynomial evaluated at `pt`:
 *   (pt^n - 1) / (pt - ω^i)
 *
 * If `zkRows > 0` the index is shifted: `actual = n - zkRows + offset`
 * (mirrors snarky-crypto's `pallas_unnormalized_lagrange_basis`). Negative
 * `actual` indices wrap via `ω^|actual|^{-1}`.
 */
export function unnormalizedLagrangeBasis(F, log2, zkRows, offset, pt) {
  const size = 1 << log2;
  const actual = zkRows > 0 ? (size - zkRows + offset) | 0 : offset | 0;
  const omega = domainGenerator(F, log2);
  const ai = actual < 0 ? -actual : actual;
  let omegaI = F.power(omega, BigInt(ai));
  if (actual < 0) {
    const inv = F.inverse(omegaI);
    if (inv === undefined) throw new Error('unnormalizedLagrangeBasis: omega^|i| not invertible');
    omegaI = inv;
  }
  // evaluate_vanishing_polynomial(pt) = pt^n - 1
  const ptN = F.power(pt, BigInt(size));
  const numerator = F.sub(ptN, 1n);
  const denom = F.sub(pt, omegaI);
  const quot = F.div(numerator, denom);
  if (quot === undefined) throw new Error('unnormalizedLagrangeBasis: division by zero');
  return quot;
}

/**
 * IPA `b_poly` bilinear form:
 *   b(x) = ∏_{i=0}^{k-1} (1 + chals[i] * x^(2^(k-1-i)))
 *
 * Mirrors `poly-commitment/src/commitment.rs:416 b_poly`.
 */
export function bPoly(F, chals, x) {
  const k = chals.length;
  if (k === 0) return 1n;
  // pow_twos[i] = x^(2^i)
  const powTwos = new Array(k);
  powTwos[0] = F.fromBigint(x);
  for (let i = 1; i < k; i++) powTwos[i] = F.square(powTwos[i - 1]);
  let acc = 1n;
  for (let i = 0; i < k; i++) {
    acc = F.mul(acc, F.add(1n, F.mul(chals[i], powTwos[k - 1 - i])));
  }
  return acc;
}

/**
 * `compute_b0` from snarky-crypto:
 *   b_poly(chals, zeta) + evalscale * b_poly(chals, zetaOmega)
 */
export function computeB0(F, chals, zeta, zetaOmega, evalscale) {
  const a = bPoly(F, chals, zeta);
  const b = bPoly(F, chals, zetaOmega);
  return F.add(a, F.mul(evalscale, b));
}
