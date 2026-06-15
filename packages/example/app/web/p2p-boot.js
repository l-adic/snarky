import "./styles.css";
// P2P proving-mesh entry. Roles + transport are chosen from the URL hash:
//   #local                         no network — drive the whole tree locally
//   #mode=base&session=S&t=bc      seed a block + publish, also help merge
//   #mode=merge&session=S&t=bc     help merge ready slots
// transports (t): bc = BroadcastChannel (same browser), manual = copy-paste SDP,
// trystero = WebRTC mesh over public relays.
//
// The worker (prover RPC service) is constructed here so vite bundles its graph.
import { mkClient, onEvent } from "../output-es/Snarky.Example.P2P.ProverClient/index.js";
import { runLocal } from "../output-es/Snarky.Example.P2P.LocalDriver/index.js";
import { startNode, Base, Merge } from "../output-es/Snarky.Example.P2P.Node/index.js";
import { initIce } from "./p2p-rtc.js";

function hashParams() {
  const raw = location.hash.replace(/^#/, "");
  const p = {};
  for (const part of raw.split("&")) {
    if (!part) continue;
    const [k, v] = part.split("=");
    p[k] = v === undefined ? true : decodeURIComponent(v);
  }
  return p;
}
const params = hashParams();
const mode = params.mode || (params.merge ? "merge" : params.base ? "base" : params.local ? "local" : "");
const session0 = params.session || "l-adic";
const tKind0 = params.t || "trystero";

// Prefill the TURN field from a previously-saved localStorage["snarky-turn"]
// (shown as the "urls|user|pass" shorthand, or raw JSON if it was an array /
// multi-server config we can't round-trip to shorthand).
function turnDisplay() {
  const raw = localStorage.getItem("snarky-turn");
  if (!raw) return "";
  try {
    const t = JSON.parse(raw);
    if (Array.isArray(t)) return raw;
    if (t && t.urls) {
      const url = Array.isArray(t.urls) ? t.urls[0] : t.urls;
      return [url, t.username, t.credential].filter(Boolean).join("|");
    }
  } catch {}
  return raw;
}
const turn0 = turnDisplay();

const app = document.getElementById("app");
const sel = (v, t, label) => `<option value="${t}"${v === t ? " selected" : ""}>${label}</option>`;
app.innerHTML = `
  <div class="app">
    <div class="header">
      <h1 class="title">snarky · P2P proving mesh</h1>
      <span id="phase" class="phase-badge">idle</span>
      <span id="role" class="phase-badge"></span>
      <label style="font:12px sans-serif;color:#94a3b8">session
        <input id="session" value="${session0}" style="width:9ch;font:12px monospace" /></label>
      <label style="font:12px sans-serif;color:#94a3b8">transport
        <select id="transport">
          ${sel(tKind0, "trystero", "Trystero · WebRTC (cross-device)")}
          ${sel(tKind0, "bc", "BroadcastChannel (same browser)")}
          ${sel(tKind0, "manual", "manual SDP (2 peers)")}
        </select></label>
      <label style="font:12px sans-serif;color:#94a3b8" title="Optional TURN relay for peers behind symmetric NAT / CGNAT. Shorthand 'turn:host:3478|user|pass', or paste a JSON {urls,username,credential}. Added to the built-in public relay.">TURN
        <input id="turn" value="${turn0}" placeholder="turn:host:3478|user|pass (optional)" style="width:24ch;font:12px monospace" /></label>
      <label style="font:12px sans-serif;color:#94a3b8">role
        <select id="role-select">
          ${sel(mode || "base", "base", "base prover (private)")}
          ${sel(mode || "base", "merge", "merge prover")}
          ${sel(mode || "base", "local", "run local (no peers)")}
        </select></label>
      <button id="start" class="run-btn">start</button>
      <button id="next" class="run-btn" style="display:none" disabled>prove next</button>
    </div>
    <div class="grid">
      <div id="tree" class="panel"><div class="panel-title">work tree</div></div>
      <div id="log" class="panel"></div>
    </div>
    <p class="footnote">proofs are computed in a wasm worker; peers exchange them over the chosen transport and verify every received proof before merging on it. leaves (base proofs) are private to the base prover; internal merge nodes are computed by any peer.</p>
  </div>`;

const logEl = document.getElementById("log");
const phaseEl = document.getElementById("phase");
const roleEl = document.getElementById("role");
let proven = 0;
const pad2 = (n) => String(n).padStart(2, "0");
function addLog(severity, text) {
  const line = document.createElement("div");
  line.className = "log-line";
  const now = new Date();
  const ts = document.createElement("span");
  ts.className = "log-time";
  ts.textContent = pad2(now.getHours()) + ":" + pad2(now.getMinutes()) + ":" + pad2(now.getSeconds());
  const sev = document.createElement("span");
  sev.className = "log-sev " + severity;
  sev.textContent = "[" + severity + "]";
  const txt = document.createElement("span");
  txt.className = "log-text";
  txt.textContent = text;
  line.append(ts, sev, txt);
  logEl.prepend(line);
  if (/merged slot/.test(text)) proven++;
  if (severity === "error") phaseEl.textContent = "failed";
}

const worker = new Worker(new URL("./p2p-worker.js", import.meta.url), { type: "module" });
// optional rayon-thread cap (#threads=N) so several provers can share a machine
if (params.threads) worker.postMessage({ config: { threads: +params.threads } });
const client = mkClient(worker)();
onEvent(client)((m) => () => {
  if (m.ev === "log") addLog(m.severity, m.text);
  else if (m.ev === "error") addLog("error", m.text);
})();

const log = (o) => () => addLog(o.severity, o.text);

const SVGNS = "http://www.w3.org/2000/svg";
const COLOR = { complete: "#22c55e", pending: "#f59e0b", locked: "#475569" };
const el = (tag, attrs, text) => { const e = document.createElementNS(SVGNS, tag); for (const k in attrs) e.setAttribute(k, attrs[k]); if (text != null) e.textContent = text; return e; };

// One block's tree as an <svg>. `statuses` is [{slot,status,by}].
function blockSvg(n, statuses) {
  const depthOf = (s) => (s <= 1 ? 0 : 1 + depthOf(s >> 1));
  const pow2 = (k) => 1 << k;
  const colW = 96, rowH = 78, width = Math.max(n * colW, 200), maxDepth = depthOf(n);
  const height = (maxDepth + 1) * rowH + 24;
  const pos = (slot) => { const d = depthOf(slot), idx = slot - pow2(d), lw = width / pow2(d); return { x: idx * lw + lw / 2, y: d * rowH + 36 }; };
  const infoOf = (slot) => statuses.find((x) => x.slot === slot) || {};
  const stOf = (slot) => infoOf(slot).status || "locked";
  const byOf = (slot) => (infoOf(slot).by || "").slice(0, 6);
  const svg = el("svg", { width, height });
  for (let s = 2; s <= 2 * n - 1; s++) { const c = pos(s), p = pos(s >> 1); svg.append(el("line", { x1: p.x, y1: p.y + 14, x2: c.x, y2: c.y - 14, stroke: "#334155", "stroke-width": 1.5 })); }
  for (let s = 1; s <= 2 * n - 1; s++) {
    const { x, y } = pos(s), st = stOf(s), isLeaf = s >= n, by = byOf(s);
    svg.append(el("circle", { cx: x, cy: y, r: 13, fill: st === "complete" ? COLOR[st] : "#1e293b", stroke: COLOR[st], "stroke-width": 2.5 }));
    svg.append(el("text", { x, y: y + 30, "text-anchor": "middle", fill: "#94a3b8", "font-size": 10 }, (isLeaf ? "tx " + (s - n) : "merge")));
    if (by) svg.append(el("text", { x, y: y + 42, "text-anchor": "middle", fill: COLOR.complete, "font-size": 9, "font-family": "monospace" }, by));
  }
  return svg;
}

// The role this peer started as ("base" | "merge" | "local"), for messaging.
let startedRole = null;

// Render every block's tree (one base prover → one block; many blocks coexist).
function renderTrees(blocks) {
  const treeEl = document.getElementById("tree");
  if (blocks.length === 0) {
    // No block exists yet anywhere this peer can see. Explain why, by role —
    // otherwise it just looks stuck at "0/0 nodes / nothing ready".
    const hint =
      startedRole === "merge"
        ? "No block yet. A <b>merge</b> prover only helps <i>after</i> a <b>base</b> peer has published a block — so at least one connected peer must be running as <b>base</b>. Waiting for a base prover to compile its circuit and generate a block (~30–60s on desktop; can be minutes on a phone)…"
        : "Compiling the circuit, then generating your block from its private transactions… (~30–60s on desktop; can be a few minutes — or fail on memory — on a phone). Your work tree appears once the block is ready; watch the log below.";
    treeEl.innerHTML =
      '<div class="panel-title">work tree</div><div class="empty" style="line-height:1.6">' + hint + "</div>";
    return;
  }
  treeEl.innerHTML = '<div class="panel-title">work trees (' + blocks.length + " block" + (blocks.length === 1 ? "" : "s") + ")</div>";
  for (const b of blocks) {
    const wrap = document.createElement("div");
    wrap.style.marginBottom = "8px";
    const lbl = document.createElement("div");
    lbl.style.cssText = "font:11px monospace;color:#64748b;margin:4px 0";
    const done = b.statuses.filter((x) => x.status === "complete").length;
    lbl.textContent = "block " + b.blockId.replace(/[^0-9]/g, "").slice(8, 16) + " · " + done + "/" + (2 * b.n - 1);
    wrap.append(lbl, blockSvg(b.n, b.statuses));
    treeEl.append(wrap);
  }
}

const onScan = (s) => () => {
  const total = s.blocks.reduce((a, b) => a + 2 * b.n - 1, 0);
  const done = s.blocks.reduce((a, b) => a + b.statuses.filter((x) => x.status === "complete").length, 0);
  if (phaseEl.textContent !== "failed")
    phaseEl.textContent =
      total === 0
        ? startedRole === "merge"
          ? "waiting for a base prover…"
          : "compiling / generating block…"
        : done === total
          ? "all blocks done ✓"
          : "running… (" + done + "/" + total + " nodes)";
  renderTrees(s.blocks);
  const next = document.getElementById("next");
  next.disabled = s.steppable === 0;
  next.textContent = s.steppable > 0 ? "prove next (" + s.steppable + " ready)" : "nothing ready";
};

// read the live selector/input values (so the URL hash is just a default)
const currentSession = () => document.getElementById("session").value.trim() || "default";
const currentTransport = () => document.getElementById("transport").value;

// Persist the TURN field to localStorage["snarky-turn"] (read by p2p-rtc's
// iceServers(), so it must be set BEFORE the transport builds its RTCPeer-
// Connection). Accepts raw JSON ({…} or […]) or the shorthand
// "turn:host:port|username|credential". Empty clears it (back to defaults).
function applyTurn() {
  const spec = document.getElementById("turn").value.trim();
  if (!spec) { localStorage.removeItem("snarky-turn"); return; }
  if (spec[0] === "{" || spec[0] === "[") {
    try { JSON.parse(spec); localStorage.setItem("snarky-turn", spec); return; }
    catch { addLog("warning", "TURN: ignoring invalid JSON"); return; }
  }
  const [urls, username, credential] = spec.split("|").map((s) => s.trim());
  if (!urls) { addLog("warning", "TURN: empty url — ignoring"); return; }
  localStorage.setItem("snarky-turn", JSON.stringify(username ? { urls, username, credential } : { urls }));
}

async function mkTransport(tKind, session) {
  if (tKind === "manual") {
    const { mkManualTransport } = await import("./p2p-transport-manual.js");
    return mkManualTransport();
  }
  if (tKind === "trystero") {
    const { mkTrysteroTransport } = await import("./p2p-transport-trystero.js");
    return mkTrysteroTransport(session);
  }
  const { mkBroadcastTransport } = await import("./p2p-transport-broadcast.js");
  return mkBroadcastTransport(session);
}

async function startMesh(isBase) {
  startedRole = isBase ? "base" : "merge";
  const session = currentSession();
  const tKind = currentTransport();
  roleEl.textContent = (isBase ? "base · " : "merge · ") + tKind + " · session " + session;
  phaseEl.textContent = "connecting…";
  document.getElementById("start").style.display = "none";
  document.getElementById("session").disabled = true;
  document.getElementById("transport").disabled = true;
  document.getElementById("role-select").disabled = true;
  applyTurn(); // persist the TURN field BEFORE the transport builds its RTCPeerConnection
  document.getElementById("turn").disabled = true;
  if (document.getElementById("turn").value.trim()) addLog("info", "using custom TURN relay (plus the built-in relays)");
  if (tKind === "bc") addLog("info", "BroadcastChannel only connects tabs of the SAME browser — pick Trystero for different browsers/machines");
  // WebRTC transports: fetch the Metered account's TURN credentials first.
  if (tKind === "trystero" || tKind === "manual") {
    const n = await initIce();
    addLog("info", n > 0 ? "loaded " + n + " TURN relay(s) from the Metered account" : "no Metered key — using built-in public TURN relay");
  }
  const transport = await mkTransport(tKind, session);
  globalThis.__transport = transport; // for manual-SDP signaling / tests
  addLog("info", "joined session '" + session + "' as " + transport.myId + " (" + startedRole + " prover) over " + tKind);
  const handle = startNode({ transport, client, mode: isBase ? Base : Merge, log, onScan })();
  globalThis.__node = handle; // for tests / manual stepping
  const next = document.getElementById("next");
  next.style.display = "";
  next.onclick = () => handle.step();
  // manual SDP has no discovery server — render the copy-paste exchange UI so
  // the two peers can hand-wire their WebRTC connection.
  if (tKind === "manual") setupManualSignaling(transport);
}

// Copy-paste SDP signaling panel (manual transport, zero infra, exactly 2 peers).
// One peer creates an offer and sends the string to the other; the other pastes
// it, returns an answer string; the first applies it. NOTE: we deliberately do
// NOT call transport.onPeer here — startNode already owns that handler (greet);
// connection success shows up as the "peer connected" log line.
function setupManualSignaling(transport) {
  const panel = document.createElement("div");
  panel.className = "panel";
  panel.id = "sdp";
  panel.style.marginBottom = "1rem";
  panel.innerHTML = `
    <div class="panel-title">manual SDP signaling — 2 peers, no server</div>
    <p class="empty" style="line-height:1.6">Pick ONE side to <b>Create offer</b>; copy the string to the other peer (any channel — chat, email). The other clicks <b>I was given an offer</b>, pastes it, and sends the <b>answer</b> string back; the offerer pastes that and clicks Apply. The channel opens and the mesh runs.</p>
    <div id="sdp-pick" style="display:flex;gap:.5rem;flex-wrap:wrap;margin:.5rem 0">
      <button id="sdp-offer" class="run-btn" style="margin-left:0">Create offer</button>
      <button id="sdp-haveoffer" class="run-btn" style="margin-left:0;background:#475569">I was given an offer</button>
    </div>
    <label id="sdp-in-wrap" class="empty" style="display:none">
      <span id="sdp-in-kind">Paste their offer</span>:
      <textarea id="sdp-in" rows="3" style="width:100%;font:11px monospace;margin:.3rem 0"></textarea>
    </label>
    <button id="sdp-apply" class="run-btn" style="margin-left:0;display:none">Apply</button>
    <label id="sdp-out-wrap" class="empty" style="display:none">
      Your <span id="sdp-out-kind">offer</span> — copy &amp; send to the other peer (click to select all):
      <textarea id="sdp-out" readonly rows="3" style="width:100%;font:11px monospace;margin:.3rem 0"></textarea>
    </label>
    <div id="sdp-status" class="empty" style="margin-top:.4rem"></div>`;
  const grid = document.querySelector(".grid");
  grid.parentNode.insertBefore(panel, grid);

  const $ = (id) => document.getElementById(id);
  const show = (el, on = true) => { el.style.display = on ? "" : "none"; };
  $("sdp-out").onclick = () => $("sdp-out").select();
  let role = null; // "offerer" | "answerer"

  $("sdp-offer").onclick = async () => {
    role = "offerer";
    show($("sdp-pick"), false);
    $("sdp-status").textContent = "gathering ICE candidates…";
    const offer = await transport.createOffer();
    $("sdp-out-kind").textContent = "offer";
    $("sdp-out").value = offer;
    show($("sdp-out-wrap"));
    $("sdp-in-kind").textContent = "Paste their answer";
    show($("sdp-in-wrap"));
    $("sdp-apply").textContent = "Apply answer";
    show($("sdp-apply"));
    $("sdp-status").textContent = "send the offer above, then paste the answer you get back.";
  };
  $("sdp-haveoffer").onclick = () => {
    role = "answerer";
    show($("sdp-pick"), false);
    $("sdp-in-kind").textContent = "Paste their offer";
    show($("sdp-in-wrap"));
    $("sdp-apply").textContent = "Accept offer & create answer";
    show($("sdp-apply"));
  };
  $("sdp-apply").onclick = async () => {
    const val = $("sdp-in").value.trim();
    if (!val) { $("sdp-status").textContent = "paste the string first."; return; }
    try {
      if (role === "answerer") {
        $("sdp-status").textContent = "gathering ICE candidates…";
        const answer = await transport.acceptOffer(val);
        $("sdp-out-kind").textContent = "answer";
        $("sdp-out").value = answer;
        show($("sdp-out-wrap"));
        show($("sdp-apply"), false);
        show($("sdp-in-wrap"), false);
        $("sdp-status").textContent = "send the answer above back to the offerer — the channel opens when they apply it.";
      } else {
        await transport.acceptAnswer(val);
        show($("sdp-apply"), false);
        show($("sdp-in-wrap"), false);
        $("sdp-status").textContent = "answer applied — establishing connection… (watch for “peer connected” in the log)";
      }
    } catch (e) {
      $("sdp-status").textContent = "error: " + (e && e.message ? e.message : e);
    }
  };
}

function startLocal() {
  startedRole = "local";
  roleEl.textContent = "local (no peers)";
  phaseEl.textContent = "running…";
  document.getElementById("start").style.display = "none";
  document.getElementById("session").disabled = true;
  document.getElementById("transport").disabled = true;
  document.getElementById("role-select").disabled = true;
  document.getElementById("turn").disabled = true;
  runLocal(client)(log)();
}

function start() {
  const role = document.getElementById("role-select").value;
  if (role === "local") startLocal();
  else startMesh(role === "base");
}
document.getElementById("start").onclick = start;

// A role in the URL hash (#mode=base / #base / #merge / #local) auto-starts —
// used by headless tests and the merge-peer launcher; a fresh page waits for
// the user to pick a role and click Start (no default-to-base).
if (mode === "local" || mode === "base" || mode === "merge") start();
