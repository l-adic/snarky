// The o1js mirror of `Bench.Pickles.Common`'s workload: an NRR base program
// plus an N=2 Tree_proof_return-shaped recursive program.
//
// Parity contract with the PS suite (packages/pickles-bench):
//   * Nrr: zero prev proofs, trivial body, publicOutput = 0.
//   * Tree: ONE branch taking [Nrr proof, Self proof] — conditional
//     verification on the Self slot (base case detected by prev output == -1,
//     exactly the PS rule's `isBaseCase` trick), output 0 (base) or prev + 1.
//   * FILLER_ITERS multiplications of two witnessed zeros pad the step circuit.
//     `npm run rows` reports tree.step's row count, which is the WHOLE step
//     circuit — recursion/IVP verification overhead included — so tuning the
//     filler until that count lands in (2^15, 2^16] sizes the *total* circuit
//     (recursion + filler) to domain 2^16, the apples-to-apples target. o1js
//     gate accounting differs from PS's, so the constant is stack-specific:
//     1<<16 fillers ⇒ 32,772 rows here vs PS's 53,960; both are domain 2^16.
import { Field, Provable, SelfProof, ZkProgram } from "o1js";

export const FILLER_ITERS = 1 << 16;

export const Nrr = ZkProgram({
  name: "bench-nrr",
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
  name: "bench-tree",
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
          const [z1, z2] = Provable.witnessFields(2, () => [0n, 0n]);
          z1.mul(z2);
        }

        return { publicOutput: out };
      },
    },
  },
});

export class TreeProof extends ZkProgram.Proof(Tree) {}

// The dummy's domainLog2 MUST equal the program's COMPILED step domain log2 — an
// exact match, not a hint. A mismatch fails the prove with 'Constraint
// unsatisfied: Checked.inv / scalars_env / prevs_verified'. With the 2^16 filler
// the compiled domain is 2^16. If FILLER_ITERS changes, re-derive this.
export const STEP_DOMAIN_LOG2 = 16;

// The base-case Self slot is a dummy proof carrying output -1 (the sentinel the
// circuit branches on), mirroring how the PS suite feeds its base prove.
export async function dummySelfProof(): Promise<SelfProof<undefined, Field>> {
  return (await TreeProof.dummy(undefined, Field(-1), 2, STEP_DOMAIN_LOG2)) as SelfProof<
    undefined,
    Field
  >;
}
