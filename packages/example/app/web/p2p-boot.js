import "./styles.css";
// P2P star worker-pool entry (main thread). Picks a role + transport from the
// URL hash or the controls, spawns the prover worker (which owns the wasm
// backend + the transport), and renders its events:
//   #role=coordinator&session=S&t=bc&poolSize=2&threads=2&auto=1
//   #role=peer&session=S&t=bc&threads=2&auto=1
// transports (t): bc = BroadcastChannel (same browser; the headless test
// vehicle), trystero = WebRTC mesh over public relays (cross-device).
//
// A coordinator is the block producer: it proves nothing, farms every base AND
// merge job to the pool of peers, and verifies the root. A peer is a full-core
// prover answering Assigns. Run one coordinator + N peers in the same session.
//
// The REAL transport is built HERE, on the main thread (it stays responsive
// while the worker proves, and WebRTC's RTCPeerConnection only works off-worker);
// it is bridged into the prover worker over postMessage (see p2p-bridge.js). The
// worker is constructed HERE too so vite bundles its module graph.
import { initIce, probeTurn } from "./p2p-rtc.js";
import { mkTransport } from "./p2p-mk-transport.js";

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
const role0 = params.role === "peer" ? "peer" : "coordinator";
const session0 = params.session || "snarky-p2p";
const tKind0 = params.t || "bc";
const poolSize0 = params.poolSize || "2";
const threads0 = params.threads || "";

const sel = (v, t, label) => `<option value="${t}"${v === t ? " selected" : ""}>${label}</option>`;
const app = document.getElementById("app");
app.innerHTML = `
  <div class="app">
    <div class="header">
      <h1 class="title">snarky · P2P star worker-pool</h1>
      <span id="phase" class="phase-badge">idle</span>
      <span id="role" class="phase-badge"></span>
      <label style="font:12px sans-serif;color:#94a3b8">role
        <select id="role-select">
          ${sel(role0, "coordinator", "coordinator (block producer)")}
          ${sel(role0, "peer", "worker peer (prover)")}
        </select></label>
      <label style="font:12px sans-serif;color:#94a3b8">session
        <input id="session" value="${session0}" style="width:11ch;font:12px monospace" /></label>
      <label style="font:12px sans-serif;color:#94a3b8">transport
        <select id="transport">
          ${sel(tKind0, "bc", "BroadcastChannel (same browser)")}
          ${sel(tKind0, "trystero", "Trystero · WebRTC (cross-device)")}
        </select></label>
      <label style="font:12px sans-serif;color:#94a3b8">peers
        <input id="poolsize" value="${poolSize0}" style="width:4ch;font:12px monospace" /></label>
      <button id="start" class="run-btn">start</button>
    </div>
    <div class="grid">
      <div id="tree" class="panel"><div class="panel-title">work tree</div></div>
      <div id="log" class="panel"></div>
    </div>
    <p class="footnote">A coordinator farms every base and merge proof to the connected worker peers over the chosen transport and verifies the root proof; peers each prove one job at a time at full core speed. Open one coordinator and N peers in the same session.</p>
  </div>`;

const logEl = document.getElementById("log");
const phaseEl = document.getElementById("phase");
const roleEl = document.getElementById("role");
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
  if (severity === "error") phaseEl.textContent = "failed";
}

const setPhase = (p) => { if (phaseEl.textContent !== "failed") phaseEl.textContent = p; window.__p2pPhase = p; };

// One block's scan-state tree as an <svg>, from the engine's onScan payload
// ({ blockId, leaves, statuses:[{slot,status}] }).
const SVGNS = "http://www.w3.org/2000/svg";
const COLOR = { complete: "#22c55e", pending: "#f59e0b", locked: "#475569" };
const el = (tag, attrs, text) => { const e = document.createElementNS(SVGNS, tag); for (const k in attrs) e.setAttribute(k, attrs[k]); if (text != null) e.textContent = text; return e; };
function blockSvg(n, statuses) {
  const depthOf = (s) => (s <= 1 ? 0 : 1 + depthOf(s >> 1));
  const pow2 = (k) => 1 << k;
  const colW = 96, rowH = 78, width = Math.max(n * colW, 200), maxDepth = depthOf(Math.max(n, 1));
  const height = (maxDepth + 1) * rowH + 24;
  const pos = (slot) => { const d = depthOf(slot), idx = slot - pow2(d), lw = width / pow2(d); return { x: idx * lw + lw / 2, y: d * rowH + 36 }; };
  const stOf = (slot) => (statuses.find((x) => x.slot === slot) || {}).status || "locked";
  const svg = el("svg", { width, height });
  for (let s = 2; s <= 2 * n - 1; s++) { const c = pos(s), p = pos(s >> 1); svg.append(el("line", { x1: p.x, y1: p.y + 14, x2: c.x, y2: c.y - 14, stroke: "#334155", "stroke-width": 1.5 })); }
  for (let s = 1; s <= 2 * n - 1; s++) {
    const { x, y } = pos(s), st = stOf(s), isLeaf = s >= n;
    svg.append(el("circle", { cx: x, cy: y, r: 13, fill: st === "complete" ? COLOR[st] : "#1e293b", stroke: COLOR[st], "stroke-width": 2.5 }));
    svg.append(el("text", { x, y: y + 30, "text-anchor": "middle", fill: "#94a3b8", "font-size": 10 }, isLeaf ? "tx " + (s - n) : "merge"));
  }
  return svg;
}
function renderScan(s) {
  const treeEl = document.getElementById("tree");
  const n = s.leaves || 0;
  const done = (s.statuses || []).filter((x) => x.status === "complete").length;
  treeEl.innerHTML = '<div class="panel-title">work tree · ' + done + "/" + Math.max(2 * n - 1, 0) + " nodes</div>";
  if (n > 0) treeEl.append(blockSvg(n, s.statuses || []));
}

// `opts` overrides the controls — used by the headless test / launchers, where
// the URL hash is authoritative (e.g. `t=manual`, which the UI select doesn't
// offer). The Start button passes nothing and reads the controls.
function startRole(opts) {
  const role = opts?.role ?? document.getElementById("role-select").value;
  const session = opts?.session ?? (document.getElementById("session").value.trim() || "snarky-p2p");
  const tKind = opts?.transport ?? document.getElementById("transport").value;
  const poolSize = opts?.poolSize ?? (+document.getElementById("poolsize").value || 2);
  roleEl.textContent = role + " · " + tKind + " · session " + session;
  setPhase("connecting…");
  for (const id of ["start", "role-select", "session", "transport", "poolsize"]) document.getElementById(id).disabled = true;
  if (tKind === "bc") addLog("info", "BroadcastChannel connects tabs of the SAME browser — pick Trystero for different machines");

  const launch = async () => {
    // The real transport lives on THIS (main) thread; the worker gets a bridged
    // proxy. So the network connection is serviced here, never blocked by the
    // worker's synchronous proving.
    const transport = await mkTransport(tKind, session);
    window.__transport = transport; // for manual-SDP signaling / tests
    const worker = new Worker(new URL("./p2p-worker.js", import.meta.url), { type: "module" });
    window.__worker = worker;
    worker.onmessage = (e) => {
      const m = e.data;
      if (!m) return;
      // worker → transport relay
      if (m._t === "broadcast") { transport.broadcast(m.msg); return; }
      if (m._t === "send") { transport.sendTo(m.peer, m.msg); return; }
      // worker → page events
      if (m.tag === "log") addLog(m.value.severity, m.value.text);
      else if (m.tag === "phase") setPhase(m.value);
      else if (m.tag === "scan") renderScan(m.value);
      else if (m.tag === "verified") {
        window.__p2pVerified = !!m.value;
        addLog(m.value ? "info" : "error", m.value ? "block root proof verified ✓" : "block root proof FAILED verification");
        setPhase(m.value ? "done ✓" : "failed");
      }
    };
    worker.onerror = (ev) => addLog("error", "[worker] " + (ev?.message || "crashed — see console"));
    // transport → worker relay (+ our id), then start the role.
    transport.onMessage((from, raw) => worker.postMessage({ _t: "msg", from, raw }));
    transport.onPeer((id) => worker.postMessage({ _t: "peer", id }));
    worker.postMessage({ _t: "myId", id: transport.myId });
    worker.postMessage({ type: "start", role, session, poolSize, threads: threads0 ? +threads0 : undefined });
  };

  // WebRTC transports: load TURN credentials + probe before connecting.
  if (tKind === "trystero") {
    initIce().then((r) => {
      addLog(r.status === "ok" ? "info" : "warning", "Metered ICE: " + r.status + (r.count ? " (" + r.count + " servers)" : ""));
      probeTurn().then(({ relay, srflx }) => addLog(relay ? "info" : "warning", "TURN probe: " + (relay ? "relay ✓" : srflx ? "srflx only" : "none")));
      launch();
    });
  } else {
    launch();
  }
}

document.getElementById("start").onclick = () => startRole();
// Auto-start for the headless test / launchers (#…&auto=1, or any explicit role).
// The hash params are authoritative here (the transport may be one the UI select
// doesn't list, e.g. manual SDP driven programmatically by the test harness).
if (params.auto || params.role) startRole({ role: role0, session: session0, transport: tKind0, poolSize: +poolSize0 || 2 });
