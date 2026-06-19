// The prover Web Worker factory. This lives at app/web/ (not in the FFI under
// output-es/) because `new URL("./p2p-worker.js", import.meta.url)` must resolve
// relative to this file's directory, and vite only discovers/bundles the worker
// graph from this exact literal. Imported by the P2P/Main FFI via the @webjs alias.
export const spawnWorker = () => new Worker(new URL("./p2p-worker.js", import.meta.url), { type: "module" });
