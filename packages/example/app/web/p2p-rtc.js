// Shared WebRTC helpers for the manual-SDP and Trystero transports.
//
// ICE: public STUN, plus a best-effort free public TURN relay so peers behind
// symmetric NAT / CGNAT (common on mobile networks) can still connect without
// us running infra. The relay only forwards DTLS-encrypted WebRTC packets, so
// it cannot read the proofs that pass through it.
//
// Primary TURN is a Metered.ca account (l-adic): initIce() fetches time-limited
// ICE servers from its credentials API at startup. The OpenRelay free public
// TURN below stays as a best-effort fallback (rate-limited, may be down). The
// relay only forwards DTLS-encrypted WebRTC packets, so it can't read proofs.
//
// Per-user / self-hosted override (tried IN ADDITION to all of the above):
//   localStorage["snarky-turn"] = JSON.stringify({urls, username, credential})
//   (an object, or an array of them).

// --- Metered.ca account ---------------------------------------------------
// The credentials API host is the account's *.metered.live domain (the relay
// servers it returns are *.relay.metered.ca). The API key is injected at BUILD
// time (VITE_METERED_API_KEY) so it is NOT committed to the repo; a per-browser
// override is localStorage["snarky-metered-key"]. NOTE: on a PUBLIC static
// deploy the key still ends up in the shipped bundle — that is inherent to a
// client-side TURN credentials call, and Metered rate-limits it to your plan.
const METERED_API = "https://l-adic.metered.live/api/v1/turn/credentials";
function meteredKey() {
  try { const k = localStorage.getItem("snarky-metered-key"); if (k) return k; } catch {}
  try { return (import.meta.env && import.meta.env.VITE_METERED_API_KEY) || ""; } catch { return ""; }
}

let meteredIce = []; // populated by initIce()

// Fetch the Metered account's ICE servers once, before any RTCPeerConnection is
// built. Best-effort: on any failure we silently keep the public fallback.
export async function initIce() {
  const key = meteredKey();
  if (!key) return 0;
  try {
    const r = await fetch(METERED_API + "?apiKey=" + encodeURIComponent(key));
    if (!r.ok) return 0;
    const list = await r.json();
    if (Array.isArray(list) && list.length) meteredIce = list;
  } catch {}
  return meteredIce.length;
}

// Verify the TURN config actually works: gather ICE candidates from a throwaway
// peer connection and report whether a `relay` candidate appears (proves a TURN
// server is reachable AND the credentials are valid) and/or a `srflx` one (STUN
// reachable). Resolves early as soon as a relay candidate shows up.
export function probeTurn(timeoutMs = 6000) {
  return new Promise((resolve) => {
    let relay = false, srflx = false, done = false;
    let pc;
    try {
      pc = new RTCPeerConnection({ iceServers: iceServers() });
    } catch {
      resolve({ relay, srflx });
      return;
    }
    const finish = () => {
      if (done) return;
      done = true;
      try { pc.close(); } catch {}
      resolve({ relay, srflx });
    };
    pc.onicecandidate = (e) => {
      if (!e.candidate) return finish(); // null candidate = gathering complete
      const c = e.candidate.candidate || "";
      if (/ typ relay /.test(c)) relay = true;
      else if (/ typ srflx /.test(c)) srflx = true;
      if (relay) finish();
    };
    pc.createDataChannel("turn-probe");
    pc.createOffer().then((o) => pc.setLocalDescription(o)).catch(finish);
    setTimeout(finish, timeoutMs);
  });
}

export function iceServers() {
  const servers = [
    { urls: "stun:stun.l.google.com:19302" },
    { urls: "stun:stun1.l.google.com:19302" },
    ...meteredIce,
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
