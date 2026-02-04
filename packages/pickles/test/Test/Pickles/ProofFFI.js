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
// Returns 12 values: [alpha, beta, gamma, zeta, ft_eval0, v, u,
//                     combined_inner_product, ft_eval1, public_eval_zeta, public_eval_zeta_omega,
//                     fq_digest]
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
    publicEvalZetaOmega: flat[10],
    fqDigest: flat[11]
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
    publicEvalZetaOmega: flat[10],
    fqDigest: flat[11]
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

// Sponge checkpoint before L/R processing
// Returns { state: [f, f, f], spongeMode: String, modeCount: Int }
export const pallasSpongeCheckpointBeforeChallenges = (proverIndex) => ({ proof, publicInput }) => {
  const checkpoint = crypto.pallasSpongeCheckpoint(proverIndex, proof, publicInput);
  return {
    state: crypto.pallasSpongeCheckpointState(checkpoint),
    spongeMode: crypto.pallasSpongeCheckpointMode(checkpoint),
    modeCount: crypto.pallasSpongeCheckpointModeCount(checkpoint)
  };
};

export const vestaSpongeCheckpointBeforeChallenges = (proverIndex) => ({ proof, publicInput }) => {
  const checkpoint = crypto.vestaSpongeCheckpoint(proverIndex, proof, publicInput);
  return {
    state: crypto.vestaSpongeCheckpointState(checkpoint),
    spongeMode: crypto.vestaSpongeCheckpointMode(checkpoint),
    modeCount: crypto.vestaSpongeCheckpointModeCount(checkpoint)
  };
};

// Proof opening L/R pairs - parse flat array into structured points
// Returns [{l: {x, y}, r: {x, y}}, ...]
const parseLrPairs = (flat) => {
  const result = [];
  for (let i = 0; i < flat.length; i += 4) {
    result.push({
      l: { x: flat[i], y: flat[i + 1] },
      r: { x: flat[i + 2], y: flat[i + 3] }
    });
  }
  return result;
};

export const pallasProofOpeningLr = (proof) =>
  parseLrPairs(crypto.pallasProofOpeningLr(proof));

export const vestaProofOpeningLr = (proof) =>
  parseLrPairs(crypto.vestaProofOpeningLr(proof));

// lr_prod: the curve point sum from bullet_reduce
// lr_prod = Σ_i [chal_inv[i] * L_i + chal[i] * R_i]
// Returns { x, y } coordinates of the result point
export const pallasProofLrProd = (proverIndex) => ({ proof, publicInput }) => {
  const coords = crypto.pallasProofLrProd(proverIndex, proof, publicInput);
  return { x: coords[0], y: coords[1] };
};

export const vestaProofLrProd = (proverIndex) => ({ proof, publicInput }) => {
  const coords = crypto.vestaProofLrProd(proverIndex, proof, publicInput);
  return { x: coords[0], y: coords[1] };
};

// Opening proof delta (curve point)
// Returns { x, y } coordinates
export const pallasProofOpeningDelta = (proof) => {
  const coords = crypto.pallasProofOpeningDelta(proof);
  return { x: coords[0], y: coords[1] };
};

export const vestaProofOpeningDelta = (proof) => {
  const coords = crypto.vestaProofOpeningDelta(proof);
  return { x: coords[0], y: coords[1] };
};

// Opening proof sg (challenge polynomial commitment, curve point)
// Returns { x, y } coordinates
export const pallasProofOpeningSg = (proof) => {
  const coords = crypto.pallasProofOpeningSg(proof);
  return { x: coords[0], y: coords[1] };
};

export const vestaProofOpeningSg = (proof) => {
  const coords = crypto.vestaProofOpeningSg(proof);
  return { x: coords[0], y: coords[1] };
};

// Opening proof z1 scalar
export const pallasProofOpeningZ1 = (proof) =>
  crypto.pallasProofOpeningZ1(proof);

export const vestaProofOpeningZ1 = (proof) =>
  crypto.vestaProofOpeningZ1(proof);

// Opening proof z2 scalar
export const pallasProofOpeningZ2 = (proof) =>
  crypto.pallasProofOpeningZ2(proof);

export const vestaProofOpeningZ2 = (proof) =>
  crypto.vestaProofOpeningZ2(proof);

// Blinding generator H from SRS
// Returns { x, y } coordinates
export const pallasProverIndexBlindingGenerator = (proverIndex) => {
  const coords = crypto.pallasProverIndexBlindingGenerator(proverIndex);
  return { x: coords[0], y: coords[1] };
};

export const vestaProverIndexBlindingGenerator = (proverIndex) => {
  const coords = crypto.vestaProverIndexBlindingGenerator(proverIndex);
  return { x: coords[0], y: coords[1] };
};

// Combined polynomial commitment (batched sum_i polyscale^i * C_i)
// Returns { x, y } coordinates
export const pallasCombinedPolynomialCommitment = (proverIndex) => ({ proof, publicInput }) => {
  const coords = crypto.pallasCombinedPolynomialCommitment(proverIndex, proof, publicInput);
  return { x: coords[0], y: coords[1] };
};

export const vestaCombinedPolynomialCommitment = (proverIndex) => ({ proof, publicInput }) => {
  const coords = crypto.vestaCombinedPolynomialCommitment(proverIndex, proof, publicInput);
  return { x: coords[0], y: coords[1] };
};

// Debug verification - prints intermediate IPA values
export const pallasDebugVerify = (proverIndex) => ({ proof, publicInput }) =>
  crypto.pallasDebugVerify(proverIndex, proof, publicInput);

export const vestaDebugVerify = (proverIndex) => ({ proof, publicInput }) =>
  crypto.vestaDebugVerify(proverIndex, proof, publicInput);
