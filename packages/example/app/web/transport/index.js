// The transport tier — the single import surface for the P2P networking glue,
// pulled from #148. Internals (rtc / broadcast / manual / trystero / bridge) are
// hidden behind this barrel; consumers import `@webjs/transport`.
//
//   mkTransport         build the REAL transport on the main thread, by kind.
//   mkBridgedTransport  the worker-side proxy that relays to the main-thread
//                       transport over postMessage (see bridge.js).
//   initIce / probeTurn WebRTC TURN-credential priming + reachability probe.
export { initIce, probeTurn } from "./rtc.js";
export { mkBridgedTransport } from "./bridge.js";

// Each kind is dynamically imported so a run that uses one transport doesn't pull
// the others' graph (e.g. the BroadcastChannel path never loads trystero).
export async function mkTransport(kind, channel) {
  if (kind === "trystero") return (await import("./trystero.js")).mkTrysteroTransport(channel);
  if (kind === "manual") return (await import("./manual.js")).mkManualTransport();
  return (await import("./broadcast.js")).mkBroadcastTransport(channel);
}
