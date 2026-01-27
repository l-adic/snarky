import { createRequire } from 'module';
const require = createRequire(import.meta.url);
const crypto = require('snarky-crypto');

// Helper: restructure flat paired array into [{zeta, omegaTimesZeta}, ...]
const pairEvals = (flat) => {
  const result = [];
  for (let i = 0; i < flat.length; i += 2) {
    result.push({ zeta: flat[i], omegaTimesZeta: flat[i + 1] });
  }
  return result;
};

// Prover index shifts
export const pallasProverIndexShifts = (proverIndex) =>
  crypto.pallasProverIndexShifts(proverIndex);

export const vestaProverIndexShifts = (proverIndex) =>
  crypto.vestaProverIndexShifts(proverIndex);

// Proof creation
export const pallasCreateProof = ({ proverIndex, witness }) =>
  crypto.pallasCreateProof(proverIndex, witness);

export const vestaCreateProof = ({ proverIndex, witness }) =>
  crypto.vestaCreateProof(proverIndex, witness);

// Proof evaluations - witness
export const pallasProofWitnessEvals = (proof) =>
  pairEvals(crypto.pallasProofWitnessEvals(proof));

export const vestaProofWitnessEvals = (proof) =>
  pairEvals(crypto.vestaProofWitnessEvals(proof));

// Proof evaluations - z (permutation polynomial)
export const pallasProofZEvals = (proof) => {
  const flat = crypto.pallasProofZEvals(proof);
  return { zeta: flat[0], omegaTimesZeta: flat[1] };
};

export const vestaProofZEvals = (proof) => {
  const flat = crypto.vestaProofZEvals(proof);
  return { zeta: flat[0], omegaTimesZeta: flat[1] };
};

// Proof evaluations - sigma
export const pallasProofSigmaEvals = (proof) =>
  pairEvals(crypto.pallasProofSigmaEvals(proof));

export const vestaProofSigmaEvals = (proof) =>
  pairEvals(crypto.vestaProofSigmaEvals(proof));

// Proof evaluations - coefficient
export const pallasProofCoefficientEvals = (proof) =>
  pairEvals(crypto.pallasProofCoefficientEvals(proof));

export const vestaProofCoefficientEvals = (proof) =>
  pairEvals(crypto.vestaProofCoefficientEvals(proof));

// Proof oracles (Fiat-Shamir)
// Returns 11 values: [alpha, beta, gamma, zeta, ft_eval0, v, u,
//                     combined_inner_product, ft_eval1, public_eval_zeta, public_eval_zeta_omega]
export const pallasProofOracles = (proverIndex) => ({ proof, publicInput }) => {
  const flat = crypto.pallasProofOracles(proverIndex, proof, publicInput);
  return {
    alpha: flat[0],
    beta: flat[1],
    gamma: flat[2],
    zeta: flat[3],
    ftEval0: flat[4],
    v: flat[5],
    u: flat[6],
    combinedInnerProduct: flat[7],
    ftEval1: flat[8],
    publicEvalZeta: flat[9],
    publicEvalZetaOmega: flat[10]
  };
};

export const vestaProofOracles = (proverIndex) => ({ proof, publicInput }) => {
  const flat = crypto.vestaProofOracles(proverIndex, proof, publicInput);
  return {
    alpha: flat[0],
    beta: flat[1],
    gamma: flat[2],
    zeta: flat[3],
    ftEval0: flat[4],
    v: flat[5],
    u: flat[6],
    combinedInnerProduct: flat[7],
    ftEval1: flat[8],
    publicEvalZeta: flat[9],
    publicEvalZetaOmega: flat[10]
  };
};

// Bulletproof challenges (IPA)
export const pallasProofBulletproofChallenges = (proverIndex) => ({ proof, publicInput }) =>
  crypto.pallasProofBulletproofChallenges(proverIndex, proof, publicInput);

export const vestaProofBulletproofChallenges = (proverIndex) => ({ proof, publicInput }) =>
  crypto.vestaProofBulletproofChallenges(proverIndex, proof, publicInput);

// Verify opening proof
export const pallasVerifyOpeningProof = (proverIndex) => ({ proof, publicInput }) =>
  crypto.pallasVerifyOpeningProof(proverIndex, proof, publicInput);

export const vestaVerifyOpeningProof = (proverIndex) => ({ proof, publicInput }) =>
  crypto.vestaVerifyOpeningProof(proverIndex, proof, publicInput);

// Permutation vanishing polynomial
export const pallasPermutationVanishingPolynomial = ({ domainLog2, zkRows, pt }) =>
  crypto.pallasPermutationVanishingPolynomial(domainLog2, zkRows, pt);

export const vestaPermutationVanishingPolynomial = ({ domainLog2, zkRows, pt }) =>
  crypto.vestaPermutationVanishingPolynomial(domainLog2, zkRows, pt);

// Domain generator
export const pallasDomainGenerator = (domainLog2) =>
  crypto.pallasDomainGenerator(domainLog2);

export const vestaDomainGenerator = (domainLog2) =>
  crypto.vestaDomainGenerator(domainLog2);

// Compute b0 = b_poly(challenges, zeta) + evalscale * b_poly(challenges, zeta_omega)
export const pallasComputeB0 = ({ challenges, zeta, zetaOmega, evalscale }) =>
  crypto.pallasComputeB0(challenges, zeta, zetaOmega, evalscale);

export const vestaComputeB0 = ({ challenges, zeta, zetaOmega, evalscale }) =>
  crypto.vestaComputeB0(challenges, zeta, zetaOmega, evalscale);

// Proof IPA rounds (domain log2)
export const pallasProofIpaRounds = (proof) =>
  crypto.pallasProofIpaRounds(proof);

export const vestaProofIpaRounds = (proof) =>
  crypto.vestaProofIpaRounds(proof);

// Proof sg commitment (for deferred IPA check)
// Returns { x, y } coordinates of the sg commitment point
export const pallasProofSg = (proof) => {
  const flat = crypto.pallasProofSg(proof);
  return { x: flat[0], y: flat[1] };
};

export const vestaProofSg = (proof) => {
  const flat = crypto.vestaProofSg(proof);
  return { x: flat[0], y: flat[1] };
};

// ─── Polynomial / Deferred Check FFI ──────────────────────────────────────────

// Create b_poly_coefficients polynomial object from IPA challenges
export const pallasBPolyCoefficients = (challenges) =>
  crypto.pallasBPolyCoefficients(challenges);

export const vestaBPolyCoefficients = (challenges) =>
  crypto.vestaBPolyCoefficients(challenges);

// Get polynomial length
export const pallasPolyLength = (poly) =>
  crypto.pallasPolyLength(poly);

export const vestaPolyLength = (poly) =>
  crypto.vestaPolyLength(poly);

// Get polynomial coefficients
export const pallasPolyGetCoeffs = (poly) =>
  crypto.pallasPolyGetCoeffs(poly);

export const vestaPolyGetCoeffs = (poly) =>
  crypto.vestaPolyGetCoeffs(poly);

// Verify deferred sg commitment check
export const pallasVerifyDeferredCheck = (proverIndex) => ({ sgX, sgY, poly }) =>
  crypto.pallasVerifyDeferredCheck(proverIndex, sgX, sgY, poly);

export const vestaVerifyDeferredCheck = (proverIndex) => ({ sgX, sgY, poly }) =>
  crypto.vestaVerifyDeferredCheck(proverIndex, sgX, sgY, poly);

// Verify deferred check entirely in Rust (for debugging)
export const pallasVerifyDeferredCheckInternal = (proverIndex) => ({ proof, publicInput }) =>
  crypto.pallasVerifyDeferredCheckInternal(proverIndex, proof, publicInput);
