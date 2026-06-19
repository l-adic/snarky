// Trystero transport: serverless WebRTC matchmaking over public Nostr relays
// (the app stays a static site — no signaling server of ours). The room is
// keyed by the session code; once peers connect the gossip Node runs over the
// data channels. Trystero handles its own chunking/binary + presence.
//
// ICE/TURN is injected from rtc.iceServers() (STUN by default, optional
// BYO TURN via localStorage["snarky-turn"]). Custom Nostr relays via
// localStorage["snarky-relays"] (JSON array); otherwise trystero's defaults.
//
// Trystero 0.25 API: makeAction returns an action OBJECT (`.send(data, {target})`
// + assignable `.onMessage`); room.onPeerJoin/onPeerLeave are assignable
// properties (not methods).
import { joinRoom, selfId } from "trystero/nostr";
import { iceServers } from "./rtc.js";

export async function mkTrysteroTransport(session) {
  let relayUrls;
  try {
    const r = JSON.parse(localStorage.getItem("snarky-relays") || "null");
    if (Array.isArray(r) && r.length) relayUrls = r;
  } catch {}
  const config = { appId: "snarky-p2p-mesh", rtcConfig: { iceServers: iceServers() } };
  if (relayUrls) config.relayUrls = relayUrls;
  const room = joinRoom(config, session);

  const gossip = room.makeAction("g");
  const peers = new Set();
  let msgHandler = null;
  let peerHandler = null;
  let peerLeaveHandler = null;
  // Track membership so onPeer (below) can replay peers that joined before the
  // handler was registered — parity with the BroadcastChannel transport, and it
  // matters here because a worker only registers its handler after its (~2 min)
  // circuit compile, by which point onPeerJoin for the coordinator has fired.
  room.onPeerJoin = (id) => { peers.add(id); if (peerHandler) peerHandler(id); };
  // A WebRTC peer's connection dropped (closed tab, crash, lost link) — surface
  // it so the coordinator drops it without waiting for a (maybe never-sent) Leave.
  room.onPeerLeave = (id) => { peers.delete(id); if (peerLeaveHandler) peerLeaveHandler(id); };
  gossip.onMessage = (data, meta) => { if (msgHandler) msgHandler(meta?.peerId ?? meta, data); };

  return {
    myId: selfId,
    broadcast: (msg) => { gossip.send(msg); },
    sendTo: (peer, msg) => { gossip.send(msg, { target: peer }); },
    onMessage: (fn) => { msgHandler = fn; },
    onPeer: (fn) => { peerHandler = fn; for (const p of peers) fn(p); },
    onPeerLeave: (fn) => { peerLeaveHandler = fn; },
  };
}
