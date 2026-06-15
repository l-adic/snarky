// Worker-thread entry for parallel snark proving. Spawned by
// `Snarky.Example.Terminal.NodeBackend` via `worker_threads`. It imports the
// compiled worker module and runs its `makeAsMain` entry, which reads the chain
// id from `workerData`, builds its own SRS + compiles the circuit, then loops
// over parentPort: decode a WorkItem, prove it, reply with the encoded proof.
//
// Like run.mjs this resolves `../output-es/` relative to its own location
// (packages/example/app/), so the simulation build (purs-backend-es) must have
// run first. node_modules / srs-cache resolve from the worker's cwd (the repo
// root, inherited from the spawning process).
import { main } from "../output-es/Snarky.Example.Terminal.SnarkWorker/index.js";
main();
