// FFI binding to the shared `bench-harness` lib (node workspace module). The PS
// side passes groups whose `prepare`/`work` are `Effect (Promise Unit)` — i.e.
// JS `() => Promise` at runtime — so the harness calls them with no glue. The
// o1js side binds the same module via index.d.ts.
import { runBench, writeArtifact } from "bench-harness";

export const runBenchImpl = (groups) => (hooks) => () => runBench(groups, hooks);
export const writeArtifactImpl = (payload) => () => writeArtifact(payload);
