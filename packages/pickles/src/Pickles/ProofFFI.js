import { createRequire } from 'module';
const require = createRequire(import.meta.url);
const crypto = require('snarky-crypto');

// Helper: restructure a Rust flat array into a chunks-array of PointEvals.
//
// Rust layout for a single polynomial (chunk-major, interleaved zeta/omega):
//   [zeta[0], zeta_omega[0], zeta[1], zeta_omega[1], ..., zeta[n-1], zeta_omega[n-1]]
//
// Result: n PointEvals, one per chunk. Validated non-empty so the PS side
// can read it as NonEmptyArray (which is a newtype wrapper over Array
// with identical runtime representation).
//
// At n=1 the result is a one-element array; at n>1, length n.
const chunksToPointEvals = (flat) => {
  if (flat.length === 0) {
    throw new Error("chunksToPointEvals: empty (num_chunks=0?)");
  }
  if (flat.length % 2 !== 0) {
    throw new Error(`chunksToPointEvals: flat length ${flat.length} not even`);
  }
  const n = flat.length / 2;
  const result = [];
  for (let c = 0; c < n; c++) {
    result.push({ zeta: flat[c * 2], omegaTimesZeta: flat[c * 2 + 1] });
  }
  return result;
};

// Multi-polynomial variant. Rust layout (polynomial-major, within-poly chunk-major):
//   [p0.zeta[0], p0.zeta_omega[0], ..., p0.zeta_omega[n-1],
//    p1.zeta[0], p1.zeta_omega[0], ..., p_{P-1}.zeta_omega[n-1]]
//
// Result: P chunks-arrays, one per polynomial. Each inner array is
// validated non-empty (NonEmptyArray on the PS side).
const polyChunksToPointEvals = (flat, numPolys) => {
  if (flat.length === 0) {
    throw new Error(`polyChunksToPointEvals(${numPolys}): empty (num_chunks=0?)`);
  }
  if (flat.length % (numPolys * 2) !== 0) {
    throw new Error(
      `polyChunksToPointEvals(${numPolys}): flat length ${flat.length} not divisible by ${numPolys * 2}`
    );
  }
  const n = flat.length / (numPolys * 2);
  const result = [];
  for (let p = 0; p < numPolys; p++) {
    const polyBase = p * 2 * n;
    const chunks = [];
    for (let c = 0; c < n; c++) {
      chunks.push({ zeta: flat[polyBase + c * 2], omegaTimesZeta: flat[polyBase + c * 2 + 1] });
    }
    result.push(chunks);
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

// Proof evaluations - witness (15 polys × n chunks × 2 points)
export const pallasProofWitnessEvals = (proof) =>
  polyChunksToPointEvals(crypto.pallasProofWitnessEvals(proof), 15);

export const vestaProofWitnessEvals = (proof) =>
  polyChunksToPointEvals(crypto.vestaProofWitnessEvals(proof), 15);

// Proof evaluations - z (permutation polynomial, 1 poly × n chunks × 2 points)
export const pallasProofZEvals = (proof) =>
  chunksToPointEvals(crypto.pallasProofZEvals(proof));

export const vestaProofZEvals = (proof) =>
  chunksToPointEvals(crypto.vestaProofZEvals(proof));

// Proof - ft_eval1 (prover-supplied evaluation of the linearization
// polynomial at zeta·omega). Lives in `proof.ft_eval1`; the verifier
// reads it directly without recomputation.
export const pallasProofFtEval1 = (proof) =>
  crypto.pallasProofFtEval1(proof);

export const vestaProofFtEval1 = (proof) =>
  crypto.vestaProofFtEval1(proof);

// Proof evaluations - sigma (6 polys × n chunks × 2 points)
export const pallasProofSigmaEvals = (proof) =>
  polyChunksToPointEvals(crypto.pallasProofSigmaEvals(proof), 6);

export const vestaProofSigmaEvals = (proof) =>
  polyChunksToPointEvals(crypto.vestaProofSigmaEvals(proof), 6);

// Proof evaluations - coefficient (15 polys × n chunks × 2 points)
export const pallasProofCoefficientEvals = (proof) =>
  polyChunksToPointEvals(crypto.pallasProofCoefficientEvals(proof), 15);

export const vestaProofCoefficientEvals = (proof) =>
  polyChunksToPointEvals(crypto.vestaProofCoefficientEvals(proof), 15);

// Proof evaluations - index (6 selectors × n chunks × 2 points)
export const pallasProofIndexEvals = (proof) =>
  polyChunksToPointEvals(crypto.pallasProofIndexEvals(proof), 6);

export const vestaProofIndexEvals = (proof) =>
  polyChunksToPointEvals(crypto.vestaProofIndexEvals(proof), 6);

// Proof oracles (Fiat-Shamir)
// Returns 16 values: [alpha, beta, gamma, zeta, ft_eval0, v, u,
//                     combined_inner_product, ft_eval1, public_eval_zeta, public_eval_zeta_omega,
//                     fq_digest, alpha_chal, zeta_chal, v_chal, u_chal]
//
// `prevChallenges` is an array of `{ sgX, sgY, challenges }` records
// (one per previous proof); we split into the three parallel arrays
// that the napi binding expects.
// Rust returns a flat Vec<F> of length `14 + 2n` where n = num_chunks.
// Layout (in order):
//   positions 0..8:         alpha, beta, gamma, zeta, ft_eval0, v, u, cip, ft_eval1
//   positions 9..9+2n-1:    [pez[0], pezo[0], pez[1], pezo[1], ..., pez[n-1], pezo[n-1]]
//   positions 9+2n..9+2n+4: fq_digest, alpha_chal, zeta_chal, v_chal, u_chal
//
// At n=1 length is 16 with fq_digest at position 11 — same as the
// pre-chunking layout, so n=1 byte-equivalence is preserved.
//
// We derive n from length, build `publicEvals` as a NonEmptyArray
// (PointEval f) validated non-empty, and read tail fields at the
// computed offset.
const unpackOracles = (flat) => {
  if (flat.length < 16 || (flat.length - 14) % 2 !== 0) {
    throw new Error(`unpackOracles: invalid length ${flat.length} (expected 14 + 2n)`);
  }
  const n = (flat.length - 14) / 2;
  const evalsStart = 9;
  const tailStart = evalsStart + 2 * n;

  const publicEvals = [];
  for (let c = 0; c < n; c++) {
    publicEvals.push({ zeta: flat[evalsStart + c * 2], omegaTimesZeta: flat[evalsStart + c * 2 + 1] });
  }
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
    publicEvals,
    fqDigest: flat[tailStart],
    alphaChal: flat[tailStart + 1],
    zetaChal: flat[tailStart + 2],
    vChal: flat[tailStart + 3],
    uChal: flat[tailStart + 4]
  };
};

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

// Lagrange commitments from SRS.
// The Rust FFI returns ALL chunks as a flat `[x0,y0,x1,y1,…]` array (length
// 2*numChunks). The `*ChunksAt` variants reshape into an array-of-points so
// PS can wrap as `Vector numChunks (AffinePoint)`. The non-`Chunks` variants
// take only the first chunk for backward compatibility with nc=1 callers.
//
// Mirrors OCaml `lagrange_commitment srs d i .unshifted` (wrap_verifier.ml:336).
export const pallasSrsLagrangeCommitmentAt = (srs) => (domainLog2) => (i) => {
  const flat = crypto.pallasSrsLagrangeCommitmentAt(srs, domainLog2, i);
  return { x: flat[0], y: flat[1] };
};

export const vestaSrsLagrangeCommitmentAt = (srs) => (domainLog2) => (i) => {
  const flat = crypto.vestaSrsLagrangeCommitmentAt(srs, domainLog2, i);
  return { x: flat[0], y: flat[1] };
};

export const pallasSrsLagrangeCommitmentChunksAt = (srs) => (domainLog2) => (i) => {
  const flat = crypto.pallasSrsLagrangeCommitmentAt(srs, domainLog2, i);
  const nc = flat.length / 2;
  const chunks = new Array(nc);
  for (let k = 0; k < nc; k++) chunks[k] = { x: flat[2 * k], y: flat[2 * k + 1] };
  return chunks;
};

export const vestaSrsLagrangeCommitmentChunksAt = (srs) => (domainLog2) => (i) => {
  const flat = crypto.vestaSrsLagrangeCommitmentAt(srs, domainLog2, i);
  const nc = flat.length / 2;
  const chunks = new Array(nc);
  for (let k = 0; k < nc; k++) chunks[k] = { x: flat[2 * k], y: flat[2 * k + 1] };
  return chunks;
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

// sigma_comm[PERMUTS-1] (the last sigma commitment). Rust emits ALL
// chunks contiguous as [chunk0.x, chunk0.y, chunk1.x, chunk1.y, ...].
// Returns Array<{x, y}> of length numChunks (= 1 for unchunked VKs).
export const pallasSigmaCommLast = (verifierIndex) => {
  const flat = crypto.pallasVerifierIndexSigmaCommLast(verifierIndex);
  const chunks = [];
  for (let i = 0; i < flat.length; i += 2) {
    chunks.push({ x: flat[i], y: flat[i + 1] });
  }
  return chunks;
};

// VK column commitments: 27 commitments (6 index + 15 coefficient + 6
// sigma) in to_batch order. Rust emits ALL chunks per commitment
// contiguously: [comm0_chunk0.x, comm0_chunk0.y, comm0_chunk1.x, ...,
// comm1_chunk0, ...]. Total flat length = 27 * numChunks * 2.
// Returns Array<Array<{x, y}>> shaped [27][numChunks]{x,y}.
const unpackVerifierIndexColumnComms = (flat) => {
  const numChunks = (flat.length / (27 * 2)) | 0;
  const result = [];
  for (let i = 0; i < 27; i++) {
    const chunks = [];
    for (let j = 0; j < numChunks; j++) {
      const off = (i * numChunks + j) * 2;
      chunks.push({ x: flat[off], y: flat[off + 1] });
    }
    result.push(chunks);
  }
  return result;
};

export const pallasVerifierIndexColumnComms = (verifierIndex) =>
  unpackVerifierIndexColumnComms(crypto.pallasVerifierIndexColumnComms(verifierIndex));

export const vestaVerifierIndexColumnComms = (verifierIndex) =>
  unpackVerifierIndexColumnComms(crypto.vestaVerifierIndexColumnComms(verifierIndex));

// sigma_comm[PERMUTS-1] for Vesta/Fq circuits. Same chunked layout as
// pallasSigmaCommLast.
export const vestaSigmaCommLast = (verifierIndex) => {
  const flat = crypto.vestaVerifierIndexSigmaCommLast(verifierIndex);
  const chunks = [];
  for (let i = 0; i < flat.length; i += 2) {
    chunks.push({ x: flat[i], y: flat[i + 1] });
  }
  return chunks;
};

// Verifier index digest for Vesta/Fq circuits
// Returns a single Fp element (Vesta.ScalarField)
export const vestaVerifierIndexDigest = (verifierIndex) =>
  crypto.vestaVerifierIndexDigest(verifierIndex);

// Parse the Rust FFI's flat coord array (Vec<Field>) into the chunked
// PS-side `ProofCommitments` shape. Rust emits the layout
//   [w0_chunk0.x, w0_chunk0.y, ..., w0_chunk{nc-1}, w1_chunk0, ..., w14_chunk{nc-1},
//    z_chunk0, ..., z_chunk{nc-1},
//    t_chunk0, ..., t_chunk{7*nc-1}]
// — 23 points × num_chunks = 46 * num_chunks coords. We derive
// num_chunks from total length; in vanilla Mina chunks=1 and the
// layout collapses to the previous flat shape.
const unpackProofCommitments = (flat) => {
  const numChunks = (flat.length / 46) | 0;
  const wComm = [];
  for (let i = 0; i < 15; i++) {
    const polyChunks = [];
    for (let j = 0; j < numChunks; j++) {
      const off = (i * numChunks + j) * 2;
      polyChunks.push({ x: flat[off], y: flat[off + 1] });
    }
    wComm.push(polyChunks);
  }
  const zComm = [];
  const zOff = 15 * numChunks * 2;
  for (let j = 0; j < numChunks; j++) {
    zComm.push({ x: flat[zOff + j * 2], y: flat[zOff + j * 2 + 1] });
  }
  const tComm = [];
  const tOff = 16 * numChunks * 2;
  const tLen = 7 * numChunks;
  for (let j = 0; j < tLen; j++) {
    tComm.push({ x: flat[tOff + j * 2], y: flat[tOff + j * 2 + 1] });
  }
  return { wComm, zComm, tComm };
};

export const vestaProofCommitments = (proof) =>
  unpackProofCommitments(crypto.vestaProofCommitments(proof));

export const pallasProofCommitments = (proof) =>
  unpackProofCommitments(crypto.pallasProofCommitments(proof));

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

