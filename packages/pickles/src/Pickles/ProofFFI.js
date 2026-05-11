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

// Proof creation (recursive case, with previous-proof accumulators)
export const pallasCreateProofWithPrev = ({ proverIndex, witness, prevChallenges }) => {
  const prevSgXs = prevChallenges.map(p => p.sgX);
  const prevSgYs = prevChallenges.map(p => p.sgY);
  const chalsList = prevChallenges.map(p => p.challenges);
  return crypto.pallasCreateProofWithPrev(proverIndex, witness, prevSgXs, prevSgYs, chalsList);
};

export const vestaCreateProofWithPrev = ({ proverIndex, witness, prevChallenges }) => {
  const prevSgXs = prevChallenges.map(p => p.sgX);
  const prevSgYs = prevChallenges.map(p => p.sgY);
  const chalsList = prevChallenges.map(p => p.challenges);
  return crypto.vestaCreateProofWithPrev(proverIndex, witness, prevSgXs, prevSgYs, chalsList);
};

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

// Proof evaluations - index (selector)
export const pallasProofIndexEvals = (proof) =>
  pairEvals(crypto.pallasProofIndexEvals(proof));

export const vestaProofIndexEvals = (proof) =>
  pairEvals(crypto.vestaProofIndexEvals(proof));

// Proof oracles (Fiat-Shamir)
// Returns 16 values: [alpha, beta, gamma, zeta, ft_eval0, v, u,
//                     combined_inner_product, ft_eval1, public_eval_zeta, public_eval_zeta_omega,
//                     fq_digest, alpha_chal, zeta_chal, v_chal, u_chal]
//
// `prevChallenges` is an array of `{ sgX, sgY, challenges }` records
// (one per previous proof); we split into the three parallel arrays
// that the napi binding expects.
const unpackOracles = (flat) => ({
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
  zetaChal: flat[13],
  vChal: flat[14],
  uChal: flat[15]
});

export const pallasProofOracles = (verifierIndex) => ({ proof, publicInput, prevChallenges }) => {
  const prevSgXs = prevChallenges.map(p => p.sgX);
  const prevSgYs = prevChallenges.map(p => p.sgY);
  const prevChals = prevChallenges.map(p => p.challenges);
  const flat = crypto.pallasProofOracles(verifierIndex, proof, publicInput, prevSgXs, prevSgYs, prevChals);
  return unpackOracles(flat);
};

export const vestaProofOracles = (verifierIndex) => ({ proof, publicInput, prevChallenges }) => {
  const prevSgXs = prevChallenges.map(p => p.sgX);
  const prevSgYs = prevChallenges.map(p => p.sgY);
  const prevChals = prevChallenges.map(p => p.challenges);
  const flat = crypto.vestaProofOracles(verifierIndex, proof, publicInput, prevSgXs, prevSgYs, prevChals);
  return unpackOracles(flat);
};

// Opening prechallenges (raw 128-bit ScalarChallenges from the IPA round loop)
export const pallasProofOpeningPrechallenges = (verifierIndex) => ({ proof, publicInput, prevChallenges }) => {
  const prevSgXs = prevChallenges.map(p => p.sgX);
  const prevSgYs = prevChallenges.map(p => p.sgY);
  const prevChals = prevChallenges.map(p => p.challenges);
  return crypto.pallasProofOpeningPrechallenges(verifierIndex, proof, publicInput, prevSgXs, prevSgYs, prevChals);
};

export const vestaProofOpeningPrechallenges = (verifierIndex) => ({ proof, publicInput, prevChallenges }) => {
  const prevSgXs = prevChallenges.map(p => p.sgX);
  const prevSgYs = prevChallenges.map(p => p.sgY);
  const prevChals = prevChallenges.map(p => p.challenges);
  return crypto.vestaProofOpeningPrechallenges(verifierIndex, proof, publicInput, prevSgXs, prevSgYs, prevChals);
};

// Bulletproof challenges (IPA)
export const pallasProofBulletproofChallenges = (verifierIndex) => ({ proof, publicInput }) =>
  crypto.pallasProofBulletproofChallenges(verifierIndex, proof, publicInput);

export const vestaProofBulletproofChallenges = (verifierIndex) => ({ proof, publicInput }) =>
  crypto.vestaProofBulletproofChallenges(verifierIndex, proof, publicInput);

// Compute kimchi's `u_t` scalar (post-CIP-absorb, pre-group_map). Used for
// byte-diffing against the wrap circuit's in-circuit sponge state.
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
// Combined polynomial commitment (batched sum_i polyscale^i * C_i)
// Returns { x, y } coordinates
// Debug verification - prints intermediate IPA values
export const pallasProverIndexDomainLog2 = (proverIndex) =>
  crypto.pallasProverIndexDomainLog2(proverIndex);

// Lagrange commitments from SRS
// Returns array of {x, y} points
// Lagrange commitments directly from SRS (no verifier index needed)
// Index-based lagrange commitment lookup (OCaml-parity for
// `Kimchi_bindings.Protocol.SRS.Fq/Fp.lagrange_commitment`).
export const pallasSrsLagrangeCommitmentAt = (srs) => (domainLog2) => (i) => {
  const flat = crypto.pallasSrsLagrangeCommitmentAt(srs, domainLog2, i);
  return { x: flat[0], y: flat[1] };
};

export const vestaSrsLagrangeCommitmentAt = (srs) => (domainLog2) => (i) => {
  const flat = crypto.vestaSrsLagrangeCommitmentAt(srs, domainLog2, i);
  return { x: flat[0], y: flat[1] };
};

// Blinding generator H directly from SRS
export const pallasSrsBlindingGenerator = (srs) => {
  const flat = crypto.pallasSrsBlindingGenerator(srs);
  return { x: flat[0], y: flat[1] };
};

export const vestaSrsBlindingGenerator = (srs) => {
  const flat = crypto.vestaSrsBlindingGenerator(srs);
  return { x: flat[0], y: flat[1] };
};

// Challenge polynomial commitment: MSM of b_poly_coefficients against SRS
// Returns { x, y } coordinates
export const vestaChallengePolyCommitment = (verifierIndex) => (challenges) => {
  const coords = crypto.vestaChallengePolyCommitment(verifierIndex, challenges);
  return { x: coords[0], y: coords[1] };
};

// ft_comm: the chunked commitment of the linearized constraint polynomial
// Returns { x, y } coordinates in Fq
// perm_scalar: the scalar multiplier for sigma_comm[PERMUTS-1] in the linearization
// Returns a single Fp element
export const pallasSigmaCommLast = (verifierIndex) => {
  const coords = crypto.pallasVerifierIndexSigmaCommLast(verifierIndex);
  return { x: coords[0], y: coords[1] };
};

// VK column commitments: 27 points (6 index + 15 coefficient + 6 sigma) in to_batch order
export const pallasVerifierIndexColumnComms = (verifierIndex) => {
  const flat = crypto.pallasVerifierIndexColumnComms(verifierIndex);
  const result = [];
  for (let i = 0; i < flat.length; i += 2) {
    result.push({ x: flat[i], y: flat[i + 1] });
  }
  return result;
};

export const vestaVerifierIndexColumnComms = (verifierIndex) => {
  const flat = crypto.vestaVerifierIndexColumnComms(verifierIndex);
  const result = [];
  for (let i = 0; i < flat.length; i += 2) {
    result.push({ x: flat[i], y: flat[i + 1] });
  }
  return result;
};

// ft_comm: the chunked commitment of the linearized constraint polynomial (Vesta/Fq circuits)
// Returns { x, y } coordinates in Fp
// perm_scalar: the scalar multiplier for sigma_comm[PERMUTS-1] in the linearization (Vesta/Fq circuits)
// Returns a single Fq element
export const vestaSigmaCommLast = (verifierIndex) => {
  const coords = crypto.vestaVerifierIndexSigmaCommLast(verifierIndex);
  return { x: coords[0], y: coords[1] };
};

// Verifier index digest for Vesta/Fq circuits
// Returns a single Fp element (Vesta.ScalarField)
export const vestaVerifierIndexDigest = (verifierIndex) =>
  crypto.vestaVerifierIndexDigest(verifierIndex);

// Proof commitments from a Pallas proof (Vesta/Fq circuits)
export const vestaProofCommitments = (proof) => {
  const flat = crypto.vestaProofCommitments(proof);
  const wComm = [];
  for (let i = 0; i < 30; i += 2) wComm.push({ x: flat[i], y: flat[i+1] });
  const zComm = { x: flat[30], y: flat[31] };
  const tComm = [];
  for (let i = 32; i < flat.length; i += 2) tComm.push({ x: flat[i], y: flat[i+1] });
  return { wComm, zComm, tComm };
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

// Construct a Pallas-committed kimchi proof from flat component data.
// PureScript-side uses `vestaMakeWireProof` in ProofFFI.purs — see that
// binding for the full field layout. Returns a *dehydrated* proof
// (prev_challenges = []); callers must call `vestaHydrateWireProof`
// before verify.
export const vestaMakeWireProof = (components) =>
  crypto.vestaMakeWireProof(
    components.wComm,
    components.zComm,
    components.tComm,
    components.lr,
    components.delta,
    components.sg,
    components.z1,
    components.z2,
    components.evals,
    components.ftEval1
  );

