// FFI for Snarky.Example.P2P.Backend. The coordinator's own prover is a nested
// Web Worker; the factory + thread hint are set by p2p-worker.js (the worker that
// runs this PS) on the global scope, because the `new Worker(new URL(...))`
// literal must live in a worker-side file vite can bundle (see p2p-worker.js).
export const spawnLocalProver = () => globalThis.__spawnProver();

export const localProverThreads = () => globalThis.__proverThreads || 0;
