// Kimchi-flavor Poseidon (Pasta / Fp) — pure-JS, atop PastaField.js.
//
// Vendored from o1js's `src/bindings/crypto/poseidon.ts` (Apache-2.0, Copyright
// o1Labs). Type-stripped. Dropped the `PoseidonLegacy` variant — we only need
// the Kimchi parameters used by Mina/proof-systems.
//
// The permutation matches `kimchi::circuits::polynomials::poseidon` /
// `mina_poseidon::permutation::full_round` exactly when parameterized with
// `poseidonParamsKimchiFp` (which we also vendor in PastaPoseidonConstants.js).
// Parity verified against kimchi-napi's `caml_pasta_fp_poseidon_block_cipher`
// in test/poseidon-parity-harness.mjs.

import { Fp, Fq } from "./PastaField.js";
import { GroupMapPallas } from "./PastaCurve.js";
import {
  poseidonParamsKimchiFp,
  poseidonParamsKimchiFq,
} from "./PastaPoseidonConstants.js";

const PoseidonFpSpec = createPoseidon(Fp, poseidonParamsKimchiFp);
const PoseidonFqSpec = createPoseidon(Fq, poseidonParamsKimchiFq);

// Pallas-base Poseidon (= Fp; the Mina application-level hash).
// `hashToGroup` is only defined for the Fp side because GroupMapPallas
// maps to Pallas points (whose coordinates live in Fp).
const Poseidon = {
  ...PoseidonFpSpec,
  hashToGroup: makeHashToGroup(PoseidonFpSpec.hash),
};

// Vesta-base Poseidon (= Fq; used by the wrap circuit's sponge).
const PoseidonFq = { ...PoseidonFqSpec };

export { Poseidon, PoseidonFq };

// ============================================================================
// Hash-to-group: feeds the field digest through GroupMapPallas. Matches o1js's
// `fieldToGroup` + `makeHashToGroup` (and the in-snark version) so out-of-snark
// callers and in-snark gadgets agree.
// ============================================================================

function fieldToGroup(x) {
  const { potentialXs, tryDecode } = GroupMapPallas;
  const xs = potentialXs(x);
  return xs.map((x) => tryDecode(x)).find((x) => x);
}

function makeHashToGroup(hash) {
  return (input) => {
    const digest = hash(input);
    const g = fieldToGroup(digest);
    if (g === undefined) return undefined;
    // The y coordinate comes from a square root, so it has two possible
    // values. To make the output deterministic, negate y if it is odd. The
    // in-snark version does the same.
    const isOdd = (g.y & 1n) === 1n;
    const y = isOdd ? Fp.negate(g.y) : g.y;
    return { x: g.x, y };
  };
}

// ============================================================================
// Poseidon constructor — assumes partial rounds = 0 (Mina/Kimchi convention).
// ============================================================================

function createPoseidon(Fp, params) {
  const {
    fullRounds,
    partialRounds,
    hasInitialRoundConstant,
    stateSize,
    rate,
    power: power_,
    roundConstants: roundConstants_,
    mds: mds_,
  } = params;

  if (partialRounds !== 0) {
    throw new Error("we don't support partial rounds");
  }
  assertPositiveInteger(rate, "rate must be a positive integer");
  assertPositiveInteger(fullRounds, "fullRounds must be a positive integer");
  assertPositiveInteger(power_, "power must be a positive integer");

  const power = BigInt(power_);
  const roundConstants = roundConstants_.map((arr) => arr.map(BigInt));
  const mds = mds_.map((arr) => arr.map(BigInt));

  function initialState() {
    return Array(stateSize).fill(0n);
  }

  function hash(input) {
    const state = update(initialState(), input);
    return state[0];
  }

  function update(state_, input) {
    const state = [...state_];
    // empty input -> single permutation on the zero state
    if (input.length === 0) {
      permutation(state);
      return state;
    }
    // pad input with zeros so its length is a multiple of the rate
    const n = Math.ceil(input.length / rate) * rate;
    input = input.concat(Array(n - input.length).fill(0n));
    // for each block of `rate` field elements, add block to the first `rate`
    // entries of the state, then permute
    for (let blockIndex = 0; blockIndex < n; blockIndex += rate) {
      for (let i = 0; i < rate; i++) {
        state[i] = Fp.add(state[i], input[blockIndex + i]);
      }
      permutation(state);
    }
    return state;
  }

  /**
   * Standard Poseidon (no partial rounds) is conceptually:
   *
   *   ARK_0 -> SBOX -> MDS
   *   ARK_1 -> SBOX -> MDS
   *   ...
   *
   * In Mina's implementation, for in-snark constraint efficiency, the first
   * round-constant addition is left out and added at the end of each round
   * instead — effectively rotating the per-round order:
   *
   *   SBOX -> MDS -> ARK_0
   *   SBOX -> MDS -> ARK_1
   *   ...
   *
   * If `hasInitialRoundConstant` is true, an extra ARK step is prepended.
   *
   * Mirrors `Snarky.Sponge.Poseidon.block_cipher` and `mina_poseidon`'s
   * `permutation::poseidon_block_cipher`.
   */
  function permutation(state) {
    let offset = 0;
    if (hasInitialRoundConstant) {
      for (let i = 0; i < stateSize; i++) {
        state[i] = Fp.add(state[i], roundConstants[0][i]);
      }
      offset = 1;
    }
    for (let round = 0; round < fullRounds; round++) {
      // S-box: state^power, element-wise
      for (let i = 0; i < stateSize; i++) {
        state[i] = Fp.power(state[i], power);
      }
      // MDS multiply (read from a stale copy so order doesn't matter)
      const oldState = [...state];
      for (let i = 0; i < stateSize; i++) {
        state[i] = Fp.dot(mds[i], oldState);
        // ARK: add this round's constants
        state[i] = Fp.add(state[i], roundConstants[round + offset][i]);
      }
    }
  }

  // -----------------------------------------------------------------
  // Granular ops — the `Poseidon.FFI.{Pallas,Vesta}` PS classes expose
  // these for callers that want to roll their own permutation (e.g.
  // `RandomOracle.Sponge.fullRound`, `Pickles.Linearization.Env`'s
  // hand-rolled MDS multiply). Kept separate from `hash`/`permutation`
  // to avoid recomputing the BigInt-converted constants per call.
  // -----------------------------------------------------------------

  // S-box: x^power. The `power` parameter is the only thing that
  // changes between Poseidon variants; for Mina-Kimchi it's 7.
  function sbox(x) {
    return Fp.power(x, power);
  }

  // MDS multiply: row-by-row dot product of `mds` with `state`.
  function applyMds(state) {
    const out = new Array(stateSize);
    for (let i = 0; i < stateSize; i++) out[i] = Fp.dot(mds[i], state);
    return out;
  }

  // One full round: `S-box -> MDS -> ARK[round + offset]`. Matches the
  // inner loop of `permutation` (above) but exposed per-round so
  // callers can fold over it. `round` is 0-indexed.
  function fullRound(state, round) {
    const sboxed = state.map((x) => Fp.power(x, power));
    const out = new Array(stateSize);
    const ark = roundConstants[round + (hasInitialRoundConstant ? 1 : 0)];
    for (let i = 0; i < stateSize; i++) {
      out[i] = Fp.add(Fp.dot(mds[i], sboxed), ark[i]);
    }
    return out;
  }

  function getRoundConstants(i) {
    return roundConstants[i + (hasInitialRoundConstant ? 1 : 0)];
  }

  return {
    initialState,
    update,
    hash,
    permutation,
    sbox,
    applyMds,
    fullRound,
    getRoundConstants,
    getNumRounds: () => fullRounds,
    getMdsMatrix: () => mds,
  };
}

// Tiny replacement for o1js's `assertPositiveInteger` — kept local to avoid
// vendoring `non-negative.ts` for a one-line check.
function assertPositiveInteger(n, msg) {
  if (!Number.isInteger(n) || n <= 0) {
    throw new Error(msg ?? `expected a positive integer, got ${n}`);
  }
}
