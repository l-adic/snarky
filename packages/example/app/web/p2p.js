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
const session = params.session || "default";
const tKind = params.t || "bc";

const app = document.getElementById("app");
app.innerHTML = `
  <div class="app">
    <div class="header">
      <h1 class="title">snarky · P2P proving mesh</h1>
      <span id="phase" class="phase-badge">idle</span>
      <span id="role" class="phase-badge"></span>
      <button id="base" class="run-btn">base prover (private)</button>
      <button id="merge" class="run-btn">merge prover</button>
      <button id="local" class="run-btn">run local (no peers)</button>
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
function addLog(severity, text) {
  const line = document.createElement("div");
  line.className = "log-line";
  const sev = document.createElement("span");
  sev.className = "log-sev " + severity;
  sev.textContent = "[" + severity + "]";
  const txt = document.createElement("span");
  txt.className = "log-text";
  txt.textContent = text;
  line.append(sev, txt);
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

// Render every block's tree (one base prover → one block; many blocks coexist).
function renderTrees(blocks) {
  const treeEl = document.getElementById("tree");
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
    phaseEl.textContent = total > 0 && done === total ? "all blocks done ✓" : "running… (" + done + "/" + total + " nodes)";
  renderTrees(s.blocks);
  const next = document.getElementById("next");
  next.disabled = s.steppable === 0;
  next.textContent = s.steppable > 0 ? "prove next (" + s.steppable + " ready)" : "nothing ready";
};

async function mkTransport() {
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
  roleEl.textContent = isBase ? "base · session " + session : "merge · session " + session;
  phaseEl.textContent = "connecting…";
  for (const b of ["base", "merge", "local"]) document.getElementById(b).style.display = "none";
  const transport = await mkTransport();
  globalThis.__transport = transport; // for manual-SDP signaling / tests
  addLog("info", "joined session '" + session + "' as " + transport.myId + " over " + tKind);
  const handle = startNode({ transport, client, mode: isBase ? Base : Merge, log, onScan })();
  globalThis.__node = handle; // for tests / manual stepping
  const next = document.getElementById("next");
  next.style.display = "";
  next.onclick = () => handle.step();
}

function startLocal() {
  phaseEl.textContent = "running…";
  for (const b of ["base", "merge", "local"]) document.getElementById(b).disabled = true;
  runLocal(client)(log)();
}

document.getElementById("base").onclick = () => startMesh(true);
document.getElementById("merge").onclick = () => startMesh(false);
document.getElementById("local").onclick = startLocal;

if (mode === "local") startLocal();
else if (mode === "base") startMesh(true);
else if (mode === "merge") startMesh(false);
