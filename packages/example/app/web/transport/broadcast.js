// Same-origin transport over BroadcastChannel: peers in tabs/contexts of the
// same browser discover + message each other with zero infrastructure. Used
// for same-machine multi-tab meshes (`#t=bc`, the infra-free way to drive
// multiple peers by hand). Exposes the Transport shape the gossip Node speaks:
// { myId, broadcast, sendTo, onMessage, onPeer }.
//
// Presence handshake: each peer announces "hello-presence"; a receiver adds the
// sender, fires onPeer, and replies "ack-presence" so both sides learn each
// other. Data frames carry {from, to?, payload}; `to` absent = broadcast.
export function mkBroadcastTransport(room) {
  const myId = Math.random().toString(36).slice(2, 10);
  const bc = new BroadcastChannel("snarky-p2p:" + room);
  const peers = new Set();
  let msgHandler = null;
  let peerHandler = null;

  const note = (id) => {
    if (id !== myId && !peers.has(id)) {
      peers.add(id);
      if (peerHandler) peerHandler(id);
    }
  };

  bc.onmessage = (e) => {
    const m = e.data;
    if (!m || m.from === myId) return;
    if (m.kind === "hello-presence") {
      note(m.from);
      bc.postMessage({ from: myId, to: m.from, kind: "ack-presence" });
      return;
    }
    if (m.kind === "ack-presence") {
      if (!m.to || m.to === myId) note(m.from);
      return;
    }
    if (m.kind === "data") {
      if (m.to && m.to !== myId) return;
      note(m.from);
      if (msgHandler) msgHandler(m.from, m.payload);
    }
  };

  const announce = () => bc.postMessage({ from: myId, kind: "hello-presence" });
  announce();
  setTimeout(announce, 250);
  setTimeout(announce, 1000);

  return {
    myId,
    broadcast: (msg) => bc.postMessage({ from: myId, kind: "data", payload: msg }),
    sendTo: (peer, msg) => bc.postMessage({ from: myId, to: peer, kind: "data", payload: msg }),
    onMessage: (fn) => { msgHandler = fn; },
    onPeer: (fn) => { peerHandler = fn; for (const p of peers) fn(p); },
    // BroadcastChannel has no connection, so no native disconnect signal — a
    // closed tab is only noticed via its `Leave` message (sent on pagehide). This
    // never fires; it exists to satisfy the Transport interface.
    onPeerLeave: (_fn) => {},
  };
}
