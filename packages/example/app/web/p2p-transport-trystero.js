// Trystero transport: serverless WebRTC matchmaking over public Nostr relays
// (the app stays a static site — no signaling server of ours). The room is
// keyed by the session code; once peers connect the gossip Node runs over the
// data channels. Trystero handles its own chunking/binary + presence.
//
// ICE/TURN is injected from p2p-rtc.iceServers() (STUN by default, optional
// BYO TURN via localStorage["snarky-turn"]). Relays overridable via
// localStorage["snarky-relays"].
import { joinRoom, selfId } from "trystero/nostr";
import { iceServers } from "./p2p-rtc.js";

const DEFAULT_RELAYS = [
  "wss://relay.damus.io",
  "wss://nos.lol",
  "wss://relay.nostr.band",
  "wss://relay.snort.social",
];

export async function mkTrysteroTransport(session) {
  let relays = null;
  try { relays = JSON.parse(localStorage.getItem("snarky-relays") || "null"); } catch {}
  const room = joinRoom(
    { appId: "snarky-p2p-mesh", relayUrls: relays || DEFAULT_RELAYS, rtcConfig: { iceServers: iceServers() } },
    session,
  );
  const [send, get] = room.makeAction("g");
  let msgHandler = null;
  let peerHandler = null;
  room.onPeerJoin((id) => { if (peerHandler) peerHandler(id); });
  get((data, peer) => { if (msgHandler) msgHandler(peer, data); });

  return {
    myId: selfId,
    broadcast: (msg) => { send(msg); },
    sendTo: (peer, msg) => { send(msg, peer); },
    onMessage: (fn) => { msgHandler = fn; },
    onPeer: (fn) => { peerHandler = fn; },
  };
}
