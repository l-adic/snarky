// The o1js mirror of Bench.Pickles.Main: two groups with the same
// shapes and labels as the PS suite —
//
//   1. "NRR + tree compile (shared warm SRS)" — compile both programs
//      per trial. o1js caches SRS/prover keys internally, so trial 1 is
//      an UNTIMED warmup (cache population = the PS suite's pre-warmed
//      SRS), then `BENCH_ITERATIONS` timed trials with
//      `forceRecompile` so each trial does full circuit synthesis.
//
//   2. "b1 recursive prove (shared warm SRS)" — compile + NRR proof +
//      b0 base proof untimed, then `PROVE_TRIALS` timed b1 merge
//      proves (each verifying [NRR proof, b0 proof]), verify gate at
//      the end.
//
// Run via tools/bench_o1js.sh (node --trace-gc) so reclaim/trial gets
// attached by the PS suite's parse_gclog.mjs.
import { Cache, setBackend, verify } from 'o1js';
import { BenchResult, Sample, stats, timedTrial, writeArtifact } from './harness.js';

// Backend selection MUST precede any ZkProgram construction, hence the
// dynamic import of programs below. 'native' = @o1js/native (napi-rs,
// native OS threads — same boundary style as our kimchi-napi, making
// it the tightest apples-to-apples pairing); 'wasm' = the default.
const BACKEND = (process.env.O1JS_BACKEND ?? 'wasm') as 'wasm' | 'native';
if (BACKEND === 'native') setBackend('native');
const { Nrr, Tree, dummySelfProof } = await import('./programs.js');

const BENCH_ITERATIONS = 3; // matches Bench.Pickles.Common.benchIterations
const PROVE_TRIALS = 6; // matches the PS prove group's window count

const COMPILE_LABEL = 'NRR + tree compile (shared warm SRS)';
const PROVE_LABEL = 'b1 recursive prove (shared warm SRS)';
console.log(`[backend] ${BACKEND}`);

async function main() {
  const o1jsVersion: string = JSON.parse(
    (await import('node:fs')).readFileSync(
      new URL(import.meta.resolve('o1js')).pathname.replace(/dist\/.*/, 'package.json'),
      'utf8'
    )
  ).version;

  // --- equivalence evidence: rows per method ------------------------
  const nrrRows = await Nrr.analyzeMethods();
  const treeRows = await Tree.analyzeMethods();
  const circuitRows: Record<string, number> = {
    'nrr.base': nrrRows.base.rows,
    'tree.step': treeRows.step.rows,
  };
  console.log('[rows]', JSON.stringify(circuitRows));

  // --- group 1: compile ---------------------------------------------
  // Cache.None everywhere: the default FileSystemDefault cache WRITES
  // the prover keys to disk on every (re)compile — for this circuit
  // that's ~650 MB (472 MB step pk + 117 MB wrap pk + NRR keys) of
  // serialization + I/O inside the timed window, which the PS compile
  // bench doesn't have. SRS + lagrange bases are unaffected: they live
  // in a separate module-level cache (`srsCache`) and a process-global
  // in-memory store, populated by the untimed warmup — so timed trials
  // measure pure synthesis + index creation, same as the PS suite.
  console.log('==> compile group: untimed warmup (SRS/lagrange population)');
  await Nrr.compile({ cache: Cache.None });
  const { verificationKey } = await Tree.compile({ cache: Cache.None });

  const compileSamples: Sample[] = [];
  for (let i = 0; i < BENCH_ITERATIONS; i++) {
    compileSamples.push(
      await timedTrial(COMPILE_LABEL, async () => {
        await Nrr.compile({ cache: Cache.None, forceRecompile: true });
        await Tree.compile({ cache: Cache.None, forceRecompile: true });
      })
    );
    console.log(`[compile trial ${i + 1}/${BENCH_ITERATIONS}] ${compileSamples[i].ms.toFixed(0)}ms`);
  }

  // --- group 2: prove ------------------------------------------------
  // The provers resident from the last compile trial are what Tree.step
  // uses; the vk was captured at warmup (compilation is deterministic —
  // method digests are bit-identical across backends, see README).
  console.log('==> prove group: untimed NRR + b0 base prove');
  const nrrProof = (await Nrr.base()).proof;
  const dummy = await dummySelfProof();
  const b0 = (await Tree.step(nrrProof, dummy)).proof; // base case: output 0

  const proveSamples: Sample[] = [];
  let lastProof = b0;
  for (let i = 0; i < PROVE_TRIALS; i++) {
    const sample = await timedTrial(PROVE_LABEL, async () => {
      lastProof = (await Tree.step(nrrProof, b0)).proof; // b1: output 1
    });
    proveSamples.push(sample);
    console.log(`[prove trial ${i + 1}/${PROVE_TRIALS}] ${sample.ms.toFixed(0)}ms`);
  }

  // verify gate (untimed sanity check, like the PS suite's checked phase)
  const ok = await verify(lastProof, verificationKey);
  if (!ok) throw new Error('b1 proof failed verification');
  console.log('[verify] b1 proof verified, publicOutput =', lastProof.publicOutput.toString());

  const benches: BenchResult[] = [
    { name: COMPILE_LABEL, samples: compileSamples, stats: stats(compileSamples) },
    { name: PROVE_LABEL, samples: proveSamples, stats: stats(proveSamples) },
  ];
  writeArtifact(o1jsVersion, BACKEND, circuitRows, benches);
}

main().then(
  () => process.exit(0),
  (e) => {
    console.error(e);
    process.exit(1);
  }
);
