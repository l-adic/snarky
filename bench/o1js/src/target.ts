// The o1js bench target: the two `bench-harness` Groups, mirroring the PS
// suite's `Bench.Pickles.Compile.group` / `Bench.Pickles.Prove.group` — same
// labels, same trial count, same prepare(untimed)/work(timed) split. No napi
// boundary, so no `Hooks` (o1js's kimchi is WASM in-heap). Drives the SAME
// `runBench` the PS side does.
import type { Group } from "bench-harness";
import { Cache, Field, SelfProof } from "o1js";
import { Nrr, Tree, dummySelfProof, NrrProof } from "./programs.js";

// = Bench.Pickles.Common.benchIterations (3). Same count both sides.
const TRIALS = 3;

const COMPILE_LABEL = "NRR + tree compile (shared warm SRS)";
const PROVE_LABEL = "b1 recursive prove (shared warm SRS)";

// Cache.None everywhere: the default FileSystemDefault cache writes ~650 MB of
// prover keys to disk on every (re)compile — I/O the PS compile bench has no
// counterpart for. SRS + lagrange bases live in o1js's own in-memory store,
// populated by the untimed warmup, so timed trials measure pure synthesis +
// index creation, same as the PS suite.
const CACHE = { cache: Cache.None as Cache };

// Equivalence evidence: rows per method (PS counterpart = compiled constraint
// count / domain log2). Must match across stacks — report it next to numbers.
export async function analyzeRows(): Promise<Record<string, number>> {
  const nrr = await Nrr.analyzeMethods();
  const tree = await Tree.analyzeMethods();
  return { "nrr.base": nrr.base.rows, "tree.step": tree.step.rows };
}

export function buildGroups(): Group[] {
  // Compile group — mirror of Compile.group: prepare warms o1js's internal
  // SRS/lagrange + keys (= the PS pre-warmed SRS, untimed); work is one full
  // forceRecompile of both programs (= fullCompile).
  const compile: Group = {
    label: COMPILE_LABEL,
    trials: TRIALS,
    prepare: async () => {
      await Nrr.compile(CACHE);
      await Tree.compile(CACHE);
    },
    work: async () => {
      await Nrr.compile({ ...CACHE, forceRecompile: true });
      await Tree.compile({ ...CACHE, forceRecompile: true });
    },
  };

  // Prove group — mirror of Prove.group: prepare compiles + proves NRR + b0
  // (untimed = prepareProve); work is one b1 merge prove on the resident prevs
  // (= the timed b1 thunk). The handles are set by prepare, read by work; like
  // the PS ref, they survive between the (single) prepare and every trial.
  let nrrProof: NrrProof;
  let b0: SelfProof<undefined, Field>;
  const prove: Group = {
    label: PROVE_LABEL,
    trials: TRIALS,
    prepare: async () => {
      await Nrr.compile(CACHE);
      await Tree.compile(CACHE);
      nrrProof = (await Nrr.base()).proof;
      const dummy = await dummySelfProof();
      b0 = (await Tree.step(nrrProof, dummy)).proof; // base case: output 0
    },
    work: async () => {
      await Tree.step(nrrProof, b0); // b1: output 1, same prevs each trial
    },
  };

  return [compile, prove];
}
