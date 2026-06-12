// The o1js mirror of `Bench.Pickles.Common`'s workload: an NRR base
// program plus an N=2 Tree_proof_return-shaped recursive program.
//
// Parity contract with the PS suite (packages/pickles-bench):
//   * Nrr: zero prev proofs, trivial body, publicOutput = 0.
//   * Tree: ONE branch taking [Nrr proof, Self proof] — conditional
//     verification on the Self slot (base case detected by prev output
//     == -1, exactly the PS rule's `isBaseCase` trick), output
//     `0` (base) or `prev + 1` (merge).
//   * FILLER_ITERS multiplications of two witnessed zeros pad the step
//     circuit. The PS suite tunes 2^16 fillers to 53,960 rows ⇒ step
//     domain 2^16. o1js gate accounting differs, so this constant MUST
//     be re-tuned: run `npm run rows` and adjust until the tree method's
//     row count lands in (2^15, 2^16]. Report rows alongside every
//     benchmark result — matching domains is what makes the comparison
//     apples-to-apples.
import { Field, Provable, SelfProof, ZkProgram, Bool } from 'o1js';

// TODO(tuning): calibrate against `npm run rows` so the Tree step
// circuit's domain log2 == 16, matching the PS workload.
export const FILLER_ITERS = 1 << 16;

export const Nrr = ZkProgram({
  name: 'bench-nrr',
  publicOutput: Field,
  methods: {
    base: {
      privateInputs: [],
      async method() {
        return { publicOutput: Field(0) };
      },
    },
  },
});

export class NrrProof extends ZkProgram.Proof(Nrr) {}

export const Tree = ZkProgram({
  name: 'bench-tree',
  publicOutput: Field,
  methods: {
    step: {
      privateInputs: [NrrProof, SelfProof],
      async method(nrrProof: NrrProof, selfProof: SelfProof<undefined, Field>) {
        // Slot 0 (NRR) verifies unconditionally, like the PS rule's
        // `proofMustVerify = [true_, not_ isBaseCase]`.
        nrrProof.verify();

        const prevOut = selfProof.publicOutput;
        const isBaseCase = prevOut.equals(Field(-1));
        selfProof.verifyIf(isBaseCase.not());

        const out = Provable.if(isBaseCase, Field(0), prevOut.add(1));

        // Filler: mirror the PS `mul_ freshZero freshZero` loop.
        for (let i = 0; i < FILLER_ITERS; i++) {
          const z1 = Provable.witness(Field, () => Field(0));
          const z2 = Provable.witness(Field, () => Field(0));
          z1.mul(z2);
        }

        return { publicOutput: out };
      },
    },
  },
});

export class TreeProof extends ZkProgram.Proof(Tree) {}

// The dummy's domainLog2 MUST equal the program's COMPILED step domain
// log2 — an exact match, not a hint. A mismatch fails the prove with
// 'Constraint unsatisfied: Checked.inv / scalars_env / prevs_verified'
// (a zero inversion in the in-circuit verifier's scalar environment;
// bisected empirically 2026-06-12: with no filler the compiled domain
// is 2^15 — the IVP wrapper alone is ~21k rows, same order as the PS
// suite's — and only 15 passes). With the 2^16 filler the compiled
// domain is 2^16. If FILLER_ITERS changes, re-derive this.
export const STEP_DOMAIN_LOG2 = 16;

// The base-case Self slot is a dummy proof carrying output -1 (the
// sentinel the circuit branches on), mirroring how the PS suite feeds
// its base prove.
export async function dummySelfProof(): Promise<SelfProof<undefined, Field>> {
  return (await TreeProof.dummy(undefined, Field(-1), 2, STEP_DOMAIN_LOG2)) as SelfProof<
    undefined,
    Field
  >;
}
