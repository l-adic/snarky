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
// Returns 14 values: [alpha, beta, gamma, zeta, ft_eval0, v, u,
//                     combined_inner_product, ft_eval1, public_eval_zeta, public_eval_zeta_omega,
//                     fq_digest, alpha_chal, zeta_chal]
export const pallasProofOracles = (verifierIndex) => ({ proof, publicInput }) => {
  const flat = crypto.pallasProofOracles(verifierIndex, proof, publicInput);
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
    fqDigest: flat[11],
    alphaChal: flat[12],
    zetaChal: flat[13]
  };
};

export const vestaProofOracles = (verifierIndex) => ({ proof, publicInput }) => {
  const flat = crypto.vestaProofOracles(verifierIndex, proof, publicInput);
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
    fqDigest: flat[11],
    alphaChal: flat[12],
    zetaChal: flat[13]
  };
};

// Bulletproof challenges (IPA)
export const pallasProofBulletproofChallenges = (verifierIndex) => ({ proof, publicInput }) =>
  crypto.pallasProofBulletproofChallenges(verifierIndex, proof, publicInput);

export const vestaProofBulletproofChallenges = (verifierIndex) => ({ proof, publicInput }) =>
  crypto.vestaProofBulletproofChallenges(verifierIndex, proof, publicInput);

// Verify opening proof
export const pallasVerifyOpeningProof = (verifierIndex) => ({ proof, publicInput }) =>
  crypto.pallasVerifyOpeningProof(verifierIndex, proof, publicInput);

export const vestaVerifyOpeningProof = (verifierIndex) => ({ proof, publicInput }) =>
  crypto.vestaVerifyOpeningProof(verifierIndex, proof, publicInput);

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
export const pallasSpongeCheckpointBeforeChallenges = (verifierIndex) => ({ proof, publicInput }) => {
  const checkpoint = crypto.pallasSpongeCheckpoint(verifierIndex, proof, publicInput);
  return {
    state: crypto.pallasSpongeCheckpointState(checkpoint),
    spongeMode: crypto.pallasSpongeCheckpointMode(checkpoint),
    modeCount: crypto.pallasSpongeCheckpointModeCount(checkpoint)
  };
};

export const vestaSpongeCheckpointBeforeChallenges = (verifierIndex) => ({ proof, publicInput }) => {
  const checkpoint = crypto.vestaSpongeCheckpoint(verifierIndex, proof, publicInput);
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
export const pallasProofLrProd = (verifierIndex) => ({ proof, publicInput }) => {
  const coords = crypto.pallasProofLrProd(verifierIndex, proof, publicInput);
  return { x: coords[0], y: coords[1] };
};

export const vestaProofLrProd = (verifierIndex) => ({ proof, publicInput }) => {
  const coords = crypto.vestaProofLrProd(verifierIndex, proof, publicInput);
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
export const pallasProverIndexBlindingGenerator = (verifierIndex) => {
  const coords = crypto.pallasProverIndexBlindingGenerator(verifierIndex);
  return { x: coords[0], y: coords[1] };
};

export const vestaProverIndexBlindingGenerator = (verifierIndex) => {
  const coords = crypto.vestaProverIndexBlindingGenerator(verifierIndex);
  return { x: coords[0], y: coords[1] };
};

// Combined polynomial commitment (batched sum_i polyscale^i * C_i)
// Returns { x, y } coordinates
export const pallasCombinedPolynomialCommitment = (verifierIndex) => ({ proof, publicInput }) => {
  const coords = crypto.pallasCombinedPolynomialCommitment(verifierIndex, proof, publicInput);
  return { x: coords[0], y: coords[1] };
};

export const vestaCombinedPolynomialCommitment = (verifierIndex) => ({ proof, publicInput }) => {
  const coords = crypto.vestaCombinedPolynomialCommitment(verifierIndex, proof, publicInput);
  return { x: coords[0], y: coords[1] };
};

// Debug verification - prints intermediate IPA values
export const pallasDebugVerify = (verifierIndex) => ({ proof, publicInput }) =>
  crypto.pallasDebugVerify(verifierIndex, proof, publicInput);

export const vestaDebugVerify = (verifierIndex) => ({ proof, publicInput }) =>
  crypto.vestaDebugVerify(verifierIndex, proof, publicInput);

// Max polynomial size from verifier index
export const pallasVerifierIndexMaxPolySize = (verifierIndex) =>
  crypto.pallasVerifierIndexMaxPolySize(verifierIndex);

export const vestaVerifierIndexMaxPolySize = (verifierIndex) =>
  crypto.vestaVerifierIndexMaxPolySize(verifierIndex);

// Verifier index digest (Fq element)
export const pallasVerifierIndexDigest = (verifierIndex) =>
  crypto.pallasVerifierIndexDigest(verifierIndex);

// Public input polynomial commitment (returns array of {x, y} points in Fq, one per chunk)
export const pallasPublicComm = (verifierIndex) => (publicInput) => {
  const flat = crypto.pallasPublicComm(verifierIndex, publicInput);
  const result = [];
  for (let i = 0; i < flat.length; i += 2) {
    result.push({ x: flat[i], y: flat[i + 1] });
  }
  return result;
};

// Lagrange commitments from SRS
// Returns array of {x, y} points
export const pallasLagrangeCommitments = (verifierIndex) => (count) => {
  const flat = crypto.pallasLagrangeCommitments(verifierIndex, count);
  const result = [];
  for (let i = 0; i < flat.length; i += 2) {
    result.push({ x: flat[i], y: flat[i + 1] });
  }
  return result;
};

export const vestaLagrangeCommitments = (verifierIndex) => (count) => {
  const flat = crypto.vestaLagrangeCommitments(verifierIndex, count);
  const result = [];
  for (let i = 0; i < flat.length; i += 2) {
    result.push({ x: flat[i], y: flat[i + 1] });
  }
  return result;
};

export const vestaPublicComm = (verifierIndex) => (publicInput) => {
  const flat = crypto.vestaPublicComm(verifierIndex, publicInput);
  const result = [];
  for (let i = 0; i < flat.length; i += 2) {
    result.push({ x: flat[i], y: flat[i + 1] });
  }
  return result;
};

// ft_comm: the chunked commitment of the linearized constraint polynomial
// Returns { x, y } coordinates in Fq
export const pallasFtComm = (verifierIndex) => ({ proof, publicInput }) => {
  const coords = crypto.pallasFtComm(verifierIndex, proof, publicInput);
  return { x: coords[0], y: coords[1] };
};

// perm_scalar: the scalar multiplier for sigma_comm[PERMUTS-1] in the linearization
// Returns a single Fp element
export const pallasPermScalar = (verifierIndex) => ({ proof, publicInput }) =>
  crypto.pallasPermScalar(verifierIndex, proof, publicInput);

// sigma_comm[PERMUTS-1]: the last sigma commitment from verifier index
// Returns { x, y } coordinates in Fq
export const pallasSigmaCommLast = (verifierIndex) => {
  const coords = crypto.pallasVerifierIndexSigmaCommLast(verifierIndex);
  return { x: coords[0], y: coords[1] };
};

// Proof commitments: w_comm (15 points), z_comm (1 point), t_comm (1+ points)
export const pallasProofCommitments = (proof) => {
  const flat = crypto.pallasProofCommitments(proof);
  const wComm = [];
  for (let i = 0; i < 30; i += 2) wComm.push({ x: flat[i], y: flat[i+1] });
  const zComm = { x: flat[30], y: flat[31] };
  const tComm = [];
  for (let i = 32; i < flat.length; i += 2) tComm.push({ x: flat[i], y: flat[i+1] });
  return { wComm, zComm, tComm };
};
