// Construct a Transport by kind — shared by the coordinator and worker-peer
// paths of p2p-worker.js. Each kind is dynamically imported so a build that only
// uses BroadcastChannel doesn't pull the WebRTC/trystero graph at runtime.
//   bc        BroadcastChannel — same-browser tabs/workers, zero infra (the
//             headless test vehicle, and the Milestone A transport).
//   trystero  WebRTC mesh over public Nostr relays — cross-device.
//   manual    a single copy-paste-signaled WebRTC data channel (2 peers).
export async function mkTransport(kind, session) {
  if (kind === "trystero") {
    const { mkTrysteroTransport } = await import("./p2p-transport-trystero.js");
    return mkTrysteroTransport(session);
  }
  if (kind === "manual") {
    const { mkManualTransport } = await import("./p2p-transport-manual.js");
    return mkManualTransport();
  }
  const { mkBroadcastTransport } = await import("./p2p-transport-broadcast.js");
  return mkBroadcastTransport(session);
}
