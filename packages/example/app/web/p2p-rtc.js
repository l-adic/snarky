// Shared WebRTC helpers for the manual-SDP and Trystero transports.
//
// ICE: public STUN, plus a best-effort free public TURN relay so peers behind
// symmetric NAT / CGNAT (common on mobile networks) can still connect without
// us running infra. The relay only forwards DTLS-encrypted WebRTC packets, so
// it cannot read the proofs that pass through it.
//
// CAVEAT: free public TURN (Metered's OpenRelay, static creds, no signup) is
// rate-limited and may be slow or down at any time — if it's unreachable ICE
// just ignores these candidates and falls back to direct/STUN. For something
// reliable, set a keyed or self-hosted (coturn) server via
//   localStorage["snarky-turn"] = JSON.stringify({urls, username, credential})
// (an object or an array of them); it is tried IN ADDITION to the defaults.
export function iceServers() {
  const servers = [
    { urls: "stun:stun.l.google.com:19302" },
    { urls: "stun:stun1.l.google.com:19302" },
    { urls: "turn:staticauth.openrelay.metered.ca:80", username: "openrelayproject", credential: "openrelayproject" },
    { urls: "turn:staticauth.openrelay.metered.ca:443", username: "openrelayproject", credential: "openrelayproject" },
    { urls: "turn:staticauth.openrelay.metered.ca:443?transport=tcp", username: "openrelayproject", credential: "openrelayproject" },
  ];
  try {
    const turn = JSON.parse(localStorage.getItem("snarky-turn") || "null");
    if (turn) return (Array.isArray(turn) ? turn : [turn]).concat(servers);
  } catch {}
  return servers;
}

// Data-channel chunking: a single proof wire can exceed the safe ~256KB SCTP
// message size, so we frame every payload into <=48KB chunks and reassemble.
// Frames: {c:msgId, i, n, d}. Ordered+reliable channel → in-order reassembly.
const CHUNK = 48 * 1024;

export function sendChunked(dc, str) {
  if (dc.readyState !== "open") return;
  const id = (dc.__sendSeq = (dc.__sendSeq || 0) + 1);
  if (str.length <= CHUNK) {
    dc.send(JSON.stringify({ c: id, i: 0, n: 1, d: str }));
    return;
  }
  const n = Math.ceil(str.length / CHUNK);
  for (let i = 0; i < n; i++) {
    dc.send(JSON.stringify({ c: id, i, n, d: str.slice(i * CHUNK, (i + 1) * CHUNK) }));
  }
}

// Wire a channel's onmessage to reassemble chunks and call onMsg(fullString).
export function recvChunked(dc, onMsg) {
  const buf = new Map(); // msgId -> {n, parts:[]}
  dc.onmessage = (e) => {
    let f;
    try { f = JSON.parse(e.data); } catch { return; }
    if (f.n === 1) { onMsg(f.d); return; }
    let rec = buf.get(f.c);
    if (!rec) { rec = { n: f.n, parts: new Array(f.n), got: 0 }; buf.set(f.c, rec); }
    if (rec.parts[f.i] === undefined) { rec.parts[f.i] = f.d; rec.got++; }
    if (rec.got === rec.n) { buf.delete(f.c); onMsg(rec.parts.join("")); }
  };
}

// Wait for ICE gathering to complete so the SDP is self-contained (no trickle —
// simplest for copy-paste signaling).
export function waitIce(pc) {
  return new Promise((resolve) => {
    if (pc.iceGatheringState === "complete") return resolve();
    const check = () => { if (pc.iceGatheringState === "complete") { pc.removeEventListener("icegatheringstatechange", check); resolve(); } };
    pc.addEventListener("icegatheringstatechange", check);
    setTimeout(resolve, 3000); // fallback: localhost gathers host candidates fast
  });
}
