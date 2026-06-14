// Manual copy-paste SDP transport: a single WebRTC data channel between two
// peers, wired by hand (or by the test harness) — zero third-party infra.
//
// Offerer:  o = await t.createOffer();  ... paste o to the answerer ...
//           await t.acceptAnswer(answer)
// Answerer: a = await t.acceptOffer(offer);  ... paste a back to the offerer
//
// Once the channel opens both sides exchange ids and the gossip Node runs over
// it exactly as over any other transport.
import { iceServers, sendChunked, recvChunked, waitIce } from "./p2p-rtc.js";

export function mkManualTransport() {
  const myId = Math.random().toString(36).slice(2, 10);
  const pc = new RTCPeerConnection({ iceServers: iceServers() });
  let dc = null;
  let remoteId = null;
  let msgHandler = null;
  let peerHandler = null;

  function bind(channel) {
    dc = channel;
    dc.onopen = () => dc.send(JSON.stringify({ c: -1, i: 0, n: 1, d: "__id:" + myId }));
    recvChunked(dc, (s) => {
      if (s.startsWith("__id:")) {
        remoteId = s.slice(5);
        if (peerHandler) peerHandler(remoteId);
        return;
      }
      if (msgHandler) msgHandler(remoteId || "peer", s);
    });
  }

  return {
    myId,
    broadcast: (msg) => { if (dc) sendChunked(dc, msg); },
    sendTo: (_peer, msg) => { if (dc) sendChunked(dc, msg); },
    onMessage: (fn) => { msgHandler = fn; },
    onPeer: (fn) => { peerHandler = fn; if (remoteId) fn(remoteId); },

    // --- signaling (driven by the UI / test harness) ---
    async createOffer() {
      bind(pc.createDataChannel("mesh", { ordered: true }));
      await pc.setLocalDescription(await pc.createOffer());
      await waitIce(pc);
      return JSON.stringify(pc.localDescription);
    },
    async acceptOffer(offer) {
      pc.ondatachannel = (e) => bind(e.channel);
      await pc.setRemoteDescription(JSON.parse(offer));
      await pc.setLocalDescription(await pc.createAnswer());
      await waitIce(pc);
      return JSON.stringify(pc.localDescription);
    },
    async acceptAnswer(answer) {
      await pc.setRemoteDescription(JSON.parse(answer));
    },
  };
}
