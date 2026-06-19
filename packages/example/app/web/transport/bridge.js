// Worker-side half of the transport bridge. The REAL transport (BroadcastChannel
// / WebRTC / trystero) lives on the MAIN thread, which stays responsive while
// this worker synchronously proves (and, for WebRTC, because RTCPeerConnection
// isn't constructable in a Worker at all). This object satisfies the `Transport`
// interface (myId / broadcast / sendTo / onMessage / onPeer) by relaying every
// operation over the worker port to the main-thread relay in p2p-boot.js.
//
// So the PureScript that runs in here (runCoordinator / runWorkerPeer) is
// transport-host-agnostic: it gets a `Transport` and never knows the real one is
// on the other thread.
//
// Frames over the port:
//   main → worker:  {_t:"myId", id} | {_t:"msg", from, raw} | {_t:"peer", id}
//                   | {_t:"leave", id}
//   worker → main:  {_t:"broadcast", msg} | {_t:"send", peer, msg}
//
// Inbound msg/peer events are BUFFERED until the role registers its handler (the
// worker boots wasm + compiles the circuit first), so nothing that arrives during
// startup is dropped.
export function mkBridgedTransport() {
  let myId = "";
  let msgHandler = null;
  let peerHandler = null;
  let peerLeaveHandler = null;
  const msgBuf = [];
  const peerBuf = [];
  const leaveBuf = [];
  let resolveReady;
  const ready = new Promise((res) => { resolveReady = res; });

  const transport = {
    get myId() { return myId; },
    broadcast: (msg) => self.postMessage({ _t: "broadcast", msg }),
    sendTo: (peer, msg) => self.postMessage({ _t: "send", peer, msg }),
    onMessage: (fn) => { msgHandler = fn; for (const [from, raw] of msgBuf.splice(0)) fn(from, raw); },
    onPeer: (fn) => { peerHandler = fn; for (const id of peerBuf.splice(0)) fn(id); },
    onPeerLeave: (fn) => { peerLeaveHandler = fn; for (const id of leaveBuf.splice(0)) fn(id); },
  };

  // Called by p2p-worker.js for every {_t:…} frame from the main relay.
  function handleMessage(m) {
    if (m._t === "myId") { myId = m.id; resolveReady(); }
    else if (m._t === "msg") { if (msgHandler) msgHandler(m.from, m.raw); else msgBuf.push([m.from, m.raw]); }
    else if (m._t === "peer") { if (peerHandler) peerHandler(m.id); else peerBuf.push(m.id); }
    else if (m._t === "leave") { if (peerLeaveHandler) peerLeaveHandler(m.id); else leaveBuf.push(m.id); }
  }

  return { transport, ready, handleMessage };
}
