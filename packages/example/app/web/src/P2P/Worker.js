// FFI for Snarky.Example.Web.P2P.Worker. The values come from globals the worker
// JS (p2p-worker.js) sets during boot, before importing this module.
export const bootRole = () => (globalThis.__p2pBoot && globalThis.__p2pBoot.role) || "peer";

export const bootChain = () => (globalThis.__p2pBoot && globalThis.__p2pBoot.chain) || "Testnet";

export const bootTransport = () => globalThis.__p2pBridge.transport;
