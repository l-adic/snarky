// kimchi-napi-backed Pickles.Prove.FFI.
//
// Field layout per PureScript convention (see `Pickles.Prove.FFI.purs`):
//   * `pallas*` = step circuit. Witness/evals in Pallas.BaseField = Fp.
//     Commits on Vesta.G. Curve coords in Vesta.BaseField = Fq.
//     kimchi-napi: `caml_pasta_fp_plonk_*` + `caml_fp_srs_*` + `fp_oracles_create`.
//   * `vesta*`  = wrap circuit. Witness/evals in Vesta.BaseField = Fq.
//     Commits on Pallas.G. Curve coords in Pallas.BaseField = Fp.
//     kimchi-napi: `caml_pasta_fq_plonk_*` + `caml_fq_srs_*` + `fq_oracles_create`.
//
// At the FFI boundary PureScript hands us JS `bigint`s for all field
// elements; kimchi-napi expects 32-byte LE `Buffer`s (`NapiPastaF{p,q}`)
// or flat `Uint8Array`s (`NapiFlatVector<F>`). The encoders below
// (`fpToBytes`, `fpFlat`, `fqFlat`, …) handle the boundary; the decoders
// (`fpFromBytes`, `fqFromBytes`) decode the bytes back to bigint.

import { createRequire } from 'module';
import { Fp, Fq, vestaEndoScalar, pallasEndoScalar } from 'pasta-runtime';

const require = createRequire(import.meta.url);
const k = require('kimchi-napi');

// ---------------------------------------------------------------------------
// Codec helpers
// ---------------------------------------------------------------------------

const fpFromBytes = (b) => Fp.fromBytesLE(b instanceof Uint8Array ? b : new Uint8Array(b));
const fqFromBytes = (b) => Fq.fromBytesLE(b instanceof Uint8Array ? b : new Uint8Array(b));
const fpToBytes = (n) => Fp.toBytesLE(n);
const fqToBytes = (n) => Fq.toBytesLE(n);

// Narrow leaf decoders: the only irreducible byte→field primitives the
// PS-side proof walk needs. PS reads the napi `WasmF{p,q}ProverProof`
// tree directly (typed foreign-record view — see this module's PS
// `NapiProof` + `decodeRawProofData`) and applies these per leaf, so the
// napi field-name surface is type-checked rather than scattered across
// untyped `.map` chains. `fp`/`fq` map to the Pasta cycle's two coord
// fields; PS picks the right one per curve-half.
export const fpFromBytesLE = (b) => fpFromBytes(b);
export const fqFromBytesLE = (b) => fqFromBytes(b);

// Identity: the napi proof handle already IS the record the PS-side
// `NapiProof` view describes. This is the one typed FFI boundary that
// asserts the napi shape; the structural decode is PS-driven from here.
export const asNapiProof = (x) => x;

// FlatVector<F> wire layout: a single Uint8Array of n*32 bytes.
function fpFlat(arr) {
  const out = new Uint8Array(arr.length * 32);
  for (let i = 0; i < arr.length; i++) out.set(fpToBytes(arr[i]), i * 32);
  return out;
}
function fqFlat(arr) {
  const out = new Uint8Array(arr.length * 32);
  for (let i = 0; i < arr.length; i++) out.set(fqToBytes(arr[i]), i * 32);
  return out;
}

// ---------------------------------------------------------------------------
// Proof creation
//
// kimchi-napi: `caml_pasta_f{p,q}_plonk_proof_create(index, witness,
//   runtime_tables, prev_challenges, prev_sgs) -> WasmF{p,q}ProverProof`.
// Pickles never uses lookups, so `runtime_tables = []`.
//
// `witness` is a `WasmVecVec` class with `.push(Uint8Array)`. For each of
// the 15 columns we concatenate the column's field elements into a flat
// 32-byte-LE buffer and push.
//
// `prev_challenges` is a single flat `NapiFlatVector<F>` (length =
// N*challenges_per_sg, see proof.rs:773); `prev_sgs` is an array of `NapiG`
// (N points). PS hands us `Array<{sgX, sgY, challenges :: Array f}>`; we
// split and flatten.
// ---------------------------------------------------------------------------

function buildWitnessFp(witness15) {
  const vv = new k.WasmVecVecFp(15);
  for (let i = 0; i < 15; i++) vv.push(fpFlat(witness15[i]));
  return vv;
}
function buildWitnessFq(witness15) {
  const vv = new k.WasmVecVecFq(15);
  for (let i = 0; i < 15; i++) vv.push(fqFlat(witness15[i]));
  return vv;
}

// ---------------------------------------------------------------------------
// KIMCHI_WITNESS_DUMP — column-major `col row value` body, gated by env.
//
// Mirrors the snarky-crypto dump hook that lived in `crypto-provider/src/
// kimchi/circuit.rs:332-346` before the slice 3.3 migration. The slice 3.3
// migration to upstream kimchi-napi dropped that path, breaking the
// witness-diff tooling (`tools/simple_chain_witness_diff.sh` etc.). We
// re-introduce it here at the JS boundary — same effect, no Rust rebuild.
//
// File layout matches the OCaml dump (`packages/pickles/test/fixtures/
// witness/ocaml_step_b0.txt` is the format reference):
//   * header lines start with `#` (we emit just `#side`, `#counter`,
//     `#columns`) — the diff tool strips them
//   * body: for col in 0..15, for row in 0..n, write `col row decimal`
//
// Counter is process-wide and shared across pallas/vesta proof_create
// calls so we mirror the OCaml ordering documented in
// `simple_chain_witness_diff.sh:10-20` (b0_step=0, b0_wrap=1, b1_step=2,
// …). `%c` in the path is substituted with the current counter; `%s` is
// substituted with `KIMCHI_WITNESS_DUMP_SIDE` if set.
// ---------------------------------------------------------------------------

let _witnessDumpCounter = 0;

function maybeDumpWitness(witnessCols15, prevChallenges) {
  const path = process.env.KIMCHI_WITNESS_DUMP;
  if (!path) return;
  const counter = _witnessDumpCounter++;
  const side = process.env.KIMCHI_WITNESS_DUMP_SIDE || "unknown";
  const file = path.replace(/%c/g, String(counter)).replace(/%s/g, side);
  // Lazy require — only paid when the env var is set.
  const fs = require("fs");
  const n = witnessCols15[0].length;
  const lines = [`#side ${side}`, `#counter ${counter}`, `#columns 15`, `#rows ${n}`];
  if (prevChallenges && prevChallenges.length > 0) {
    lines.push(`#prev_challenges ${prevChallenges.length}`);
    for (let i = 0; i < prevChallenges.length; i++) {
      const p = prevChallenges[i];
      lines.push(`#prev_challenges.${i}.sg.x ${p.sgX.toString()}`);
      lines.push(`#prev_challenges.${i}.sg.y ${p.sgY.toString()}`);
      for (let j = 0; j < p.challenges.length; j++) {
        lines.push(`#prev_challenges.${i}.chals.${j} ${p.challenges[j].toString()}`);
      }
    }
  }
  for (let col = 0; col < 15; col++) {
    const column = witnessCols15[col];
    for (let row = 0; row < n; row++) {
      lines.push(`${col} ${row} ${column[row].toString()}`);
    }
  }
  fs.writeFileSync(file, lines.join("\n") + "\n");
}

function flattenPrev(prev, encodeField, encodeCoord) {
  // Concat all prev.challenges into one Uint8Array; collect sg points.
  if (prev.length === 0) {
    return { flatChals: new Uint8Array(0), sgs: [] };
  }
  // All prev entries must have the same challenges length (kimchi-napi
  // computes `challenges_per_sg = total_len / sgs_len`).
  const perSg = prev[0].challenges.length;
  const flatChals = new Uint8Array(prev.length * perSg * 32);
  const sgs = new Array(prev.length);
  for (let i = 0; i < prev.length; i++) {
    const chals = prev[i].challenges;
    if (chals.length !== perSg) {
      throw new Error(
        `createProofWithPrev: prev_challenges lengths must agree (entry 0 = ${perSg}, entry ${i} = ${chals.length})`
      );
    }
    for (let j = 0; j < perSg; j++) {
      flatChals.set(encodeField(chals[j]), (i * perSg + j) * 32);
    }
    sgs[i] = { x: encodeCoord(prev[i].sgX), y: encodeCoord(prev[i].sgY), infinity: false };
  }
  return { flatChals, sgs };
}

export const pallasCreateProof = ({ proverIndex, witness }) => {
  maybeDumpWitness(witness, []);
  const w = buildWitnessFp(witness);
  return k.caml_pasta_fp_plonk_proof_create(proverIndex, w, [], new Uint8Array(0), []);
};

export const vestaCreateProof = ({ proverIndex, witness }) => {
  maybeDumpWitness(witness, []);
  const w = buildWitnessFq(witness);
  return k.caml_pasta_fq_plonk_proof_create(proverIndex, w, [], new Uint8Array(0), []);
};

export const pallasCreateProofWithPrev = ({ proverIndex, witness, prevChallenges }) => {
  maybeDumpWitness(witness, prevChallenges);
  const w = buildWitnessFp(witness);
  // step (pallas*): chals in Fp (field), sg coords in Fq (curve base).
  const { flatChals, sgs } = flattenPrev(prevChallenges, fpToBytes, fqToBytes);
  return k.caml_pasta_fp_plonk_proof_create(proverIndex, w, [], flatChals, sgs);
};

export const vestaCreateProofWithPrev = ({ proverIndex, witness, prevChallenges }) => {
  maybeDumpWitness(witness, prevChallenges);
  const w = buildWitnessFq(witness);
  // wrap (vesta*): chals in Fq, sg coords in Fp.
  const { flatChals, sgs } = flattenPrev(prevChallenges, fqToBytes, fpToBytes);
  return k.caml_pasta_fq_plonk_proof_create(proverIndex, w, [], flatChals, sgs);
};

// ---------------------------------------------------------------------------
// Proof verification
//
// kimchi-napi's verify takes the proof (which carries public input
// internally as `proof.public_`). PS-side public input is unused — it must
// match the bytes already inside the proof.
// ---------------------------------------------------------------------------

// Both verify paths take `publicInput` alongside the proof. The napi
// `caml_pasta_f{p,q}_plonk_proof_verify` reads the public input from
// `proof.public_` directly, so callers must inject the caller-supplied
// input (cloning the proof first to avoid mutating the caller's handle).
// Same pattern as `pallas/vestaProofOracles`; see `withInjectedInputs`
// above. Without this, a proof loaded via `*_plonk_proof_from_json`
// carries `public_=[]` (the field is `#[serde(skip)]` on
// kimchi's `ProverProof` derive) and verify silently runs against the
// wrong commitment.
export const pallasVerifyOpeningProof = (verifierIndex) => ({ proof, publicInput }) => {
  const p = withInjectedInputs(proof, publicInput, [],
    k.WasmFpPolyComm, fpToBytes, fqToBytes, k.caml_pasta_fp_plonk_proof_deep_copy);
  return k.caml_pasta_fp_plonk_proof_verify(verifierIndex, p);
};

export const vestaVerifyOpeningProof = (verifierIndex) => ({ proof, publicInput }) => {
  const p = withInjectedInputs(proof, publicInput, [],
    k.WasmFqPolyComm, fqToBytes, fpToBytes, k.caml_pasta_fq_plonk_proof_deep_copy);
  return k.caml_pasta_fq_plonk_proof_verify(verifierIndex, p);
};

export const pallasVerifyOpeningProofsBatch = (verifierIndex) => (entries) => {
  if (entries.length === 0) return true;
  const indexes = entries.map(() => verifierIndex);
  const proofs = entries.map((e) => withInjectedInputs(e.proof, e.publicInput, [],
    k.WasmFpPolyComm, fpToBytes, fqToBytes, k.caml_pasta_fp_plonk_proof_deep_copy));
  return k.caml_pasta_fp_plonk_proof_batch_verify(indexes, proofs);
};

export const vestaVerifyOpeningProofsBatch = (verifierIndex) => (entries) => {
  if (entries.length === 0) return true;
  const indexes = entries.map(() => verifierIndex);
  const proofs = entries.map((e) => withInjectedInputs(e.proof, e.publicInput, [],
    k.WasmFqPolyComm, fqToBytes, fpToBytes, k.caml_pasta_fq_plonk_proof_deep_copy));
  return k.caml_pasta_fq_plonk_proof_batch_verify(indexes, proofs);
};

// ---------------------------------------------------------------------------
// Oracles
//
// kimchi-napi's `f{p,q}_oracles_create(lgr_comm, vi, proof)` does the
// Fiat-Shamir replay. It does NOT take a separate public-input or
// prev-challenges argument — the proof itself carries them (in
// `proof.public_` and `proof.prev_challenges_*`). When pickles needs to
// inject a different prev-challenge set (e.g. the verifier-side
// "outer" challenges for the wrap-verifier's transcript replay), we
// clone the proof via `caml_pasta_*_plonk_proof_deep_copy` and overwrite
// `prev_challenges_*` via the setters before passing to oracles_create.
//
// `lgr_comm` is `NapiVector<NapiPolyComm>` of length `public_size`; each
// entry is the chunked SRS lagrange commitment for that public-input
// index. We loop `caml_f{p,q}_srs_lagrange_commitment(srs, n, i)`.
// ---------------------------------------------------------------------------

function lgrCommFp(vi) {
  const domainSize = 1 << vi.domain.log_size_of_group;
  const publicSize = vi.public_;
  const out = new Array(publicSize);
  for (let i = 0; i < publicSize; i++) {
    out[i] = k.caml_fp_srs_lagrange_commitment(vi.srs, domainSize, i);
  }
  return out;
}
function lgrCommFq(vi) {
  const domainSize = 1 << vi.domain.log_size_of_group;
  const publicSize = vi.public_;
  const out = new Array(publicSize);
  for (let i = 0; i < publicSize; i++) {
    out[i] = k.caml_fq_srs_lagrange_commitment(vi.srs, domainSize, i);
  }
  return out;
}

// Inject caller-supplied public input + prev_challenges into a fresh clone
// of the proof. Mirrors snarky-crypto's `proof_for_oracles` block
// (circuit.rs:726-739) which clones the proof and overwrites both
// `public_` and `prev_challenges` before running oracles. Pickles uses this
// to replay the Fiat-Shamir transcript against the *outer* verifier-known
// values rather than whatever the proof originally carried — critically for
// the base case where the dummy wrap proof's internal `public_` is empty
// but the wrap VK expects `vi.public_` entries.
//
// kimchi-napi `fq_oracles_create` reads `proof.public` (length =
// `proof.public.len()`) to know how many lagrange-basis chunks to MSM
// against (`oracles.rs:207`). If we don't override `public_`, the MSM
// degrades to the identity point and the Fq sponge absorbs the wrong
// `p_comm` — silently corrupting every downstream oracle (beta/gamma/
// alpha_chal/zeta_chal/digest).
function withInjectedInputs(proof, publicInput, prev, polyCommCtor, encodeField, encodeCoord, deepCopy) {
  const needClone = prev.length > 0 || publicInput.length > 0;
  if (!needClone) return proof;
  const cloned = deepCopy(proof);

  // Public input override: pack the caller-supplied scalars into the flat
  // 32n-byte buffer the `set_public_` setter expects.
  if (publicInput.length > 0) {
    const flat = new Uint8Array(publicInput.length * 32);
    for (let i = 0; i < publicInput.length; i++) {
      flat.set(encodeField(publicInput[i]), i * 32);
    }
    cloned.set_public_ = flat;
  }

  // Prev_challenges override: scalars grouped per-prev-proof; comms one
  // `polyCommCtor` per prev-proof's sg.
  if (prev.length > 0) {
    const { flatChals, sgs } = flattenPrev(prev, encodeField, encodeCoord);
    const perSg = prev[0].challenges.length;
    const vv = proof.constructor.name === 'WasmFpProverProof'
      ? new k.WasmVecVecFp(prev.length)
      : new k.WasmVecVecFq(prev.length);
    for (let i = 0; i < prev.length; i++) {
      vv.push(flatChals.slice(i * perSg * 32, (i + 1) * perSg * 32));
    }
    // napi-rs `#[napi(setter)]` exposes JS *property setters*, not methods:
    // assign with `=`, do not call.
    cloned.set_prev_challenges_scalars = vv;

    // `polyCommCtor` is the curve-correct constructor: wrap proof commits
    // on Pallas → WasmFqPolyComm; step proof commits on Vesta → WasmFpPolyComm.
    const comms = sgs.map((sg) => new polyCommCtor([sg], null));
    cloned.set_prev_challenges_comms = comms;
  }

  return cloned;
}

function decodeOracles(o, fieldDecode) {
  // SizedF 128 — PS expects a `bigint` value embedded in `f` representing
  // a 128-bit number. kimchi-napi returns the inner 128-bit scalar as a
  // full-field bigint (top bits zero); we just decode and pass through.
  // The PS-side `SizedF 128` is a phantom-tagged bigint, runtime ≈ bigint.
  return {
    alpha: fieldDecode(o.o.alpha),
    beta: fieldDecode(o.o.beta),
    gamma: fieldDecode(o.o.gamma),
    zeta: fieldDecode(o.o.zeta),
    v: fieldDecode(o.o.v),
    u: fieldDecode(o.o.u),
    alphaChal: fieldDecode(o.o.alpha_chal),
    zetaChal: fieldDecode(o.o.zeta_chal),
    vChal: fieldDecode(o.o.v_chal),
    uChal: fieldDecode(o.o.u_chal),
    fqDigest: fieldDecode(o.digest_before_evaluations),
    // `ftEval1` is also on the proof; we copy it from the proof's
    // `ft_eval1` field at the consumer site (pallasProofOracles below).
    // Keeping it on `OraclesResult` for back-compat with the PS API.
    ftEval1: undefined, // filled in by the caller
  };
}

// `pallasProofOracles` (step proofs, Vesta commits) — prev_challenges_comms
// are PolyComm<Vesta> = `WasmFpPolyComm`.
export const pallasProofOracles = (verifierIndex) => ({ proof, publicInput, prevChallenges }) => {
  const lgrComm = lgrCommFp(verifierIndex);
  const p = withInjectedInputs(proof, publicInput, prevChallenges,
    k.WasmFpPolyComm, fpToBytes, fqToBytes, k.caml_pasta_fp_plonk_proof_deep_copy);
  const o = k.fp_oracles_create(lgrComm, verifierIndex, p);
  const out = decodeOracles(o, fpFromBytes);
  out.ftEval1 = fpFromBytes(p.ft_eval1);
  return out;
};

// `vestaProofOracles` (wrap proofs, Pallas commits) — prev_challenges_comms
// are PolyComm<Pallas> = `WasmFqPolyComm`.
export const vestaProofOracles = (verifierIndex) => ({ proof, publicInput, prevChallenges }) => {
  const lgrComm = lgrCommFq(verifierIndex);
  const p = withInjectedInputs(proof, publicInput, prevChallenges,
    k.WasmFqPolyComm, fqToBytes, fpToBytes, k.caml_pasta_fq_plonk_proof_deep_copy);
  const o = k.fq_oracles_create(lgrComm, verifierIndex, p);
  const out = decodeOracles(o, fqFromBytes);
  out.ftEval1 = fqFromBytes(p.ft_eval1);
  return out;
};

// ---------------------------------------------------------------------------
// Opening prechallenges (raw 128-bit `ScalarChallenge.inner()` values from
// the IPA round loop, before endo expansion).
// ---------------------------------------------------------------------------

function decodeFlat(decodeField, flatBytes) {
  const n = flatBytes.length / 32;
  const out = new Array(n);
  for (let i = 0; i < n; i++) {
    out[i] = decodeField(flatBytes.subarray(i * 32, (i + 1) * 32));
  }
  return out;
}

export const pallasProofOpeningPrechallenges = (verifierIndex) => ({ proof, publicInput, prevChallenges }) => {
  const lgrComm = lgrCommFp(verifierIndex);
  const p = withInjectedInputs(proof, publicInput, prevChallenges,
    k.WasmFpPolyComm, fpToBytes, fqToBytes, k.caml_pasta_fp_plonk_proof_deep_copy);
  const o = k.fp_oracles_create(lgrComm, verifierIndex, p);
  return decodeFlat(fpFromBytes, o.opening_prechallenges);
};

export const vestaProofOpeningPrechallenges = (verifierIndex) => ({ proof, publicInput, prevChallenges }) => {
  const lgrComm = lgrCommFq(verifierIndex);
  const p = withInjectedInputs(proof, publicInput, prevChallenges,
    k.WasmFqPolyComm, fqToBytes, fpToBytes, k.caml_pasta_fq_plonk_proof_deep_copy);
  const o = k.fq_oracles_create(lgrComm, verifierIndex, p);
  return decodeFlat(fqFromBytes, o.opening_prechallenges);
};

// ---------------------------------------------------------------------------
// Bulletproof challenges (endo-expanded `ScalarChallenge.to_field(endo_r)`).
//
// `to_field(c, endo_r)` follows kimchi's `ScalarChallenge::to_field` with
// `length_in_bits = 128`: walk the 64 pairs of bits, accumulating `r =
// 2*r + (if hi then s else -s)` where `s = 1 + (if lo then endo_r else 1)`.
// Mirrors `proof-systems/poly-commitment/src/utils.rs:to_field` and the
// PS-side `Pickles.IPA.toField` in-circuit reproduction.
// ---------------------------------------------------------------------------

function toFieldEndo(F, chal, endoR) {
  // Read bits LSB-first; pair them up `(lo, hi)` over 64 rounds (= 128 bits).
  let r = 0n;
  let c = chal & ((1n << 128n) - 1n); // restrict to 128 bits (defensive)
  for (let i = 63; i >= 0; i--) {
    const hi = (c >> BigInt(2 * i + 1)) & 1n;
    const lo = (c >> BigInt(2 * i)) & 1n;
    const s = lo === 1n ? F.add(1n, endoR) : F.add(1n, F.fromBigint(F.modulus - 1n));
    r = F.add(F.mul(r, 2n), hi === 1n ? s : F.fromBigint(F.modulus - s));
  }
  return r;
}

export const pallasProofBulletproofChallenges = (verifierIndex) => ({ proof, publicInput, prevChallenges }) => {
  const prechals = pallasProofOpeningPrechallenges(verifierIndex)({ proof, publicInput, prevChallenges: prevChallenges || [] });
  // step-side endo_r = Pallas.endo_scalar (`Step_inner_curve.scalar`) — used
  // for the IPA challenge expansion. (See `memory/endo` notes for the
  // base-vs-scalar distinction.)
  return prechals.map((c) => toFieldEndo(Fp, c, pallasEndoScalar));
};

export const vestaProofBulletproofChallenges = (verifierIndex) => ({ proof, publicInput, prevChallenges }) => {
  const prechals = vestaProofOpeningPrechallenges(verifierIndex)({ proof, publicInput, prevChallenges: prevChallenges || [] });
  return prechals.map((c) => toFieldEndo(Fq, c, vestaEndoScalar));
};

// ---------------------------------------------------------------------------
// Prover-index domain log2 (used by Pickles to size IPA / linearization).
// ---------------------------------------------------------------------------

export const pallasProverIndexDomainLog2 = (proverIndex) => {
  const size = k.caml_pasta_fp_plonk_index_domain_d1_size(proverIndex);
  return Math.log2(size) | 0;
};

export const vestaProverIndexDomainLog2 = (proverIndex) => {
  const size = k.caml_pasta_fq_plonk_index_domain_d1_size(proverIndex);
  return Math.log2(size) | 0;
};

// ---------------------------------------------------------------------------
// SRS extractors — `pallas*` lives on Vesta SRS, `vesta*` on Pallas SRS.
// Returns coords in the COMMITMENT curve's base field (= opposite cycle
// half from the witness field).
// ---------------------------------------------------------------------------

function pcToAffinePoints(pc, decode) {
  return pc.unshifted.map((p) => ({ x: decode(p.x), y: decode(p.y) }));
}

export const pallasSrsLagrangeCommitmentChunksAt = (crs) => (domainLog2) => (i) => {
  const pc = k.caml_fp_srs_lagrange_commitment(crs.srs, 1 << domainLog2, i);
  return pcToAffinePoints(pc, fqFromBytes);
};

export const vestaSrsLagrangeCommitmentChunksAt = (crs) => (domainLog2) => (i) => {
  const pc = k.caml_fq_srs_lagrange_commitment(crs.srs, 1 << domainLog2, i);
  return pcToAffinePoints(pc, fpFromBytes);
};

export const pallasSrsBlindingGenerator = (crs) => {
  const h = k.caml_fp_srs_h(crs.srs);
  return { x: fqFromBytes(h.x), y: fqFromBytes(h.y) };
};

export const vestaSrsBlindingGenerator = (crs) => {
  const h = k.caml_fq_srs_h(crs.srs);
  return { x: fpFromBytes(h.x), y: fpFromBytes(h.y) };
};

// Vesta-side challenge polynomial commitment (the b_poly MSM against SRS).
// kimchi-napi has `caml_fq_srs_b_poly_commitment(srs, chals_flat) ->
// NapiPolyComm`. Wrap-circuit consumers expect a single AffinePoint
// `Vesta.ScalarField` (= Fp) — return the first chunk.
export const vestaChallengePolyCommitment = (verifierIndex) => (challenges) => {
  const pc = k.caml_fq_srs_b_poly_commitment(verifierIndex.srs, fqFlat(challenges));
  const p = pc.unshifted[0];
  return { x: fpFromBytes(p.x), y: fpFromBytes(p.y) };
};

// ---------------------------------------------------------------------------
// Verifier-index extractors — read structured fields from
// `NapiPlonkVerifierIndex` directly (the snarky-kimchi VerifierIndex is
// already this kimchi-napi shape after the slice 3.3 migration).
// ---------------------------------------------------------------------------

// `sigma_comm[PERMUTS-1]` — the last sigma commitment, chunked.
export const pallasSigmaCommLast = (verifierIndex) =>
  pcToAffinePoints(verifierIndex.evals.sigma_comm[6], fqFromBytes);

export const vestaSigmaCommLast = (verifierIndex) =>
  pcToAffinePoints(verifierIndex.evals.sigma_comm[6], fpFromBytes);

// 27 VK column commitments in `to_batch` order: 6 selectors + 15
// coefficients + 6 sigmas. Returns `[27][numChunks]{x,y}`.
function extractColumnComms(vi, decode) {
  const ev = vi.evals;
  const result = [
    pcToAffinePoints(ev.generic_comm, decode),
    pcToAffinePoints(ev.psm_comm, decode),
    pcToAffinePoints(ev.complete_add_comm, decode),
    pcToAffinePoints(ev.mul_comm, decode),
    pcToAffinePoints(ev.emul_comm, decode),
    pcToAffinePoints(ev.endomul_scalar_comm, decode),
  ];
  for (let i = 0; i < 15; i++) result.push(pcToAffinePoints(ev.coefficients_comm[i], decode));
  for (let i = 0; i < 6; i++) result.push(pcToAffinePoints(ev.sigma_comm[i], decode));
  return result;
}

export const pallasVerifierIndexColumnComms = (verifierIndex) =>
  extractColumnComms(verifierIndex, fqFromBytes);

export const vestaVerifierIndexColumnComms = (verifierIndex) =>
  extractColumnComms(verifierIndex, fpFromBytes);

// `vestaMakeWireProof` — assembles a `WasmFqProverProof` from PS-supplied
// flat coordinate / scalar arrays. PureScript analog of OCaml
// `Wrap_wire_proof.to_kimchi_proof`; used by `Pickles.Proof.Dummy` to
// build the base-case dummy wrap proof that recursive provers feed into
// the wrap circuit when there is no prior proof.
//
// The proof is a wrap proof (commits on Pallas):
//   * curve coords in Pallas.BaseField = Vesta.ScalarField = Fp
//   * scalars in Vesta.BaseField = Pallas.ScalarField = Fq
//
// Input field layout (all non-chunked, num_chunks = 1, WrapIPARounds = 15):
//   wComm   : 30 Fp coords = 15 × (x, y)
//   zComm   :  2 Fp coords =  1 × (x, y)
//   tComm   : 14 Fp coords =  7 × (x, y)  — t-poly's 7 quotient chunks
//   lr      : 60 Fp coords = 15 × (l.x, l.y, r.x, r.y)
//   delta   :  2 Fp coords =  1 × (x, y)
//   sg      :  2 Fp coords =  1 × (x, y)
//   z1, z2  : Fq scalars
//   evals   : 86 Fq scalars in `Pickles.Proof.Dummy` order — w[15],
//             coefficients[15], z, sigma[6], index[6]; each polynomial's
//             entry is the `(zeta, zetaOmega)` pair interleaved.
//   ftEval1 : Fq scalar
//
// `evals.public` is set to a single-chunk zero PointEvaluations: the
// kimchi `proof.oracles` call expects `Some(...)` (the prover unconditionally
// populates `public`), and zero matches the empty-public-input case in
// kimchi's `verifier.rs:351-352`.
export const vestaMakeWireProof = (c) => {
  // Build a single Pallas point from two flat-array entries (x, y).
  const pt = (arr, i) => ({ x: fpToBytes(arr[i]), y: fpToBytes(arr[i + 1]), infinity: false });
  const polyComm1 = (p) => new k.WasmFqPolyComm([p], null);

  // commitments
  const wCommArr = new Array(15);
  for (let i = 0; i < 15; i++) wCommArr[i] = polyComm1(pt(c.wComm, i * 2));
  const zCommPC = polyComm1(pt(c.zComm, 0));
  const tCommUnshifted = new Array(7);
  for (let i = 0; i < 7; i++) tCommUnshifted[i] = pt(c.tComm, i * 2);
  const tCommPC = new k.WasmFqPolyComm(tCommUnshifted, null);
  const commitments = new k.WasmFqProverCommitments(wCommArr, zCommPC, tCommPC, null);

  // opening proof
  const lr_0 = new Array(15);
  const lr_1 = new Array(15);
  for (let i = 0; i < 15; i++) {
    lr_0[i] = pt(c.lr, i * 4);
    lr_1[i] = pt(c.lr, i * 4 + 2);
  }
  const opening = new k.WasmFqOpeningProof(
    lr_0, lr_1, pt(c.delta, 0), fqToBytes(c.z1), fqToBytes(c.z2), pt(c.sg, 0),
  );

  // evals — parse the flat array. Each polynomial's PointEvaluations
  // becomes a single-chunk `{zeta: [bytes], zetaOmega: [bytes]}`.
  let off = 0;
  const pe = () => {
    const r = { zeta: [fqToBytes(c.evals[off])], zetaOmega: [fqToBytes(c.evals[off + 1])] };
    off += 2;
    return r;
  };
  const wEvals = new Array(15);
  for (let i = 0; i < 15; i++) wEvals[i] = pe();
  const coeffEvals = new Array(15);
  for (let i = 0; i < 15; i++) coeffEvals[i] = pe();
  const zEval = pe();
  const sigmaEvals = new Array(6);
  for (let i = 0; i < 6; i++) sigmaEvals[i] = pe();
  const idx = new Array(6);
  for (let i = 0; i < 6; i++) idx[i] = pe();

  const zeroPe = () => ({ zeta: [fqToBytes(0n)], zetaOmega: [fqToBytes(0n)] });
  // napi-rs `Option<T>` on an `#[napi(object)]` field requires `undefined`
  // for None — passing `null` fails with "Cannot convert undefined or null
  // to object". `lookup_sorted` is a non-optional NapiVector of Options;
  // `[]` works (an empty vector). Field names are camelCase by napi default.
  const evalsObj = {
    public: zeroPe(),
    w: wEvals,
    z: zEval,
    s: sigmaEvals,
    coefficients: coeffEvals,
    genericSelector: idx[0],
    poseidonSelector: idx[1],
    completeAddSelector: idx[2],
    mulSelector: idx[3],
    emulSelector: idx[4],
    endomulScalarSelector: idx[5],
    rangeCheck0Selector: undefined,
    rangeCheck1Selector: undefined,
    foreignFieldAddSelector: undefined,
    foreignFieldMulSelector: undefined,
    xorSelector: undefined,
    rotSelector: undefined,
    lookupAggregation: undefined,
    lookupTable: undefined,
    lookupSorted: [null, null, null, null, null],
    runtimeLookupTable: undefined,
    runtimeLookupTableSelector: undefined,
    xorLookupSelector: undefined,
    lookupGateLookupSelector: undefined,
    rangeCheckLookupSelector: undefined,
    foreignFieldMulLookupSelector: undefined,
  };

  // Empty public-input + prev_challenges for the dummy.
  return new k.WasmFqProverProof(
    commitments,
    opening,
    evalsObj,
    fqToBytes(c.ftEval1),
    new Uint8Array(0),
    new k.WasmVecVecFq(0),
    [],
  );
};
