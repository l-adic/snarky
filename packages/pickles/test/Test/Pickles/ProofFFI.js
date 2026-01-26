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

// Sponge checkpoint (squeeze value after oracles + absorbing cip)
export const pallasProofSpongeCheckpoint = (proverIndex) => ({ proof, publicInput }) =>
  crypto.pallasProofSpongeCheckpoint(proverIndex, proof, publicInput);

export const vestaProofSpongeCheckpoint = (proverIndex) => ({ proof, publicInput }) =>
  crypto.vestaProofSpongeCheckpoint(proverIndex, proof, publicInput);

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

// ─── Opening proof components ─────────────────────────────────────────────────

// Helper: restructure flat LR array into [{l: {x, y}, r: {x, y}}, ...]
// Input: [L0.x, L0.y, R0.x, R0.y, L1.x, L1.y, R1.x, R1.y, ...]
const pairLR = (flat) => {
  const result = [];
  for (let i = 0; i < flat.length; i += 4) {
    result.push({
      l: { x: flat[i], y: flat[i + 1] },
      r: { x: flat[i + 2], y: flat[i + 3] }
    });
  }
  return result;
};

// Proof L/R pairs
export const pallasProofLr = (proof) =>
  pairLR(crypto.pallasProofLr(proof));

export const vestaProofLr = (proof) =>
  pairLR(crypto.vestaProofLr(proof));

// Proof delta commitment
export const pallasProofDelta = (proof) => {
  const flat = crypto.pallasProofDelta(proof);
  return { x: flat[0], y: flat[1] };
};

export const vestaProofDelta = (proof) => {
  const flat = crypto.vestaProofDelta(proof);
  return { x: flat[0], y: flat[1] };
};

// Proof z1 scalar
export const pallasProofZ1 = (proof) =>
  crypto.pallasProofZ1(proof);

export const vestaProofZ1 = (proof) =>
  crypto.vestaProofZ1(proof);

// Proof z2 scalar
export const pallasProofZ2 = (proof) =>
  crypto.pallasProofZ2(proof);

export const vestaProofZ2 = (proof) =>
  crypto.vestaProofZ2(proof);

// Proof sg commitment
export const pallasProofSg = (proof) => {
  const flat = crypto.pallasProofSg(proof);
  return { x: flat[0], y: flat[1] };
};

export const vestaProofSg = (proof) => {
  const flat = crypto.vestaProofSg(proof);
  return { x: flat[0], y: flat[1] };
};

// Prover index H generator
export const pallasProverIndexH = (proverIndex) => {
  const flat = crypto.pallasProverIndexH(proverIndex);
  return { x: flat[0], y: flat[1] };
};

export const vestaProverIndexH = (proverIndex) => {
  const flat = crypto.vestaProverIndexH(proverIndex);
  return { x: flat[0], y: flat[1] };
};

// Proof IPA rounds (domain log2)
export const pallasProofIpaRounds = (proof) =>
  crypto.pallasProofIpaRounds(proof);

export const vestaProofIpaRounds = (proof) =>
  crypto.vestaProofIpaRounds(proof);

// Bullet reduction product lr_prod = sum(chal_inv[i] * L[i] + chal[i] * R[i])
export const pallasProofLrProd = (proverIndex) => ({ proof, publicInput }) => {
  const flat = crypto.pallasProofLrProd(proverIndex, proof, publicInput);
  return { x: flat[0], y: flat[1] };
};

export const vestaProofLrProd = (proverIndex) => ({ proof, publicInput }) => {
  const flat = crypto.vestaProofLrProd(proverIndex, proof, publicInput);
  return { x: flat[0], y: flat[1] };
};
