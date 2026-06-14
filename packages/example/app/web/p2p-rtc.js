// Shared WebRTC helpers for the manual-SDP and Trystero transports.
//
// ICE: public STUN by default; a TURN relay can be injected via
// localStorage["snarky-turn"] = JSON.stringify({urls,username,credential})
// for peers behind symmetric NAT (the static-site stays infra-free by default).
export function iceServers() {
  const stun = [{ urls: "stun:stun.l.google.com:19302" }, { urls: "stun:stun1.l.google.com:19302" }];
  try {
    const turn = JSON.parse(localStorage.getItem("snarky-turn") || "null");
    if (turn) return stun.concat(Array.isArray(turn) ? turn : [turn]);
  } catch {}
  return stun;
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
