// Merge server for the PRIVACY split (client base-proves, server merges).
// Exposes POST /merge backed by a resident compiled circuit on the NATIVE
// kimchi backend (default, fast). The browser computes the per-transaction
// base proofs locally (private inputs never leave) and POSTs only the proofs
// + public ledger statements here; the server reconstructs them and reduces
// the merge tree to a verified block root.
//
// The VK is a pure function of circuit + SRS, so a native-server merge
// verifies the wasm-client base proofs. The vite dev server serves the page
// and proxies /merge to this process (see web/vite.config.mjs), so the
// browser sees a same-origin endpoint.
//
//   node packages/example/web/merge-server.mjs            # listens on :8099
import http from "node:http";
import * as MergeServer from "../output-es/Snarky.Example.MergeServer/index.js";

const PORT = Number(process.env.PORT || 8099);

// Compiled circuit, filled in asynchronously after the port is bound (so a
// port conflict fails fast, before the slow compile). /merge returns 503
// until `state` is ready.
let state = null;
let compileError = null;

const json = (res, code, obj) =>
  res.writeHead(code, { "Content-Type": "application/json" }).end(JSON.stringify(obj));

const server = http.createServer((req, res) => {
  if (req.method !== "POST" || req.url !== "/merge") {
    json(res, 404, { error: "not found — only POST /merge is served here" });
    return;
  }
  if (compileError) {
    json(res, 503, { error: "merge server failed to compile: " + compileError });
    return;
  }
  if (!state) {
    json(res, 503, { error: "merge server still compiling — retry shortly" });
    return;
  }
  let body = "";
  req.on("data", (c) => (body += c));
  req.on("end", () => {
    try {
      const { leaves } = JSON.parse(body);
      const t0 = Date.now();
      const result = MergeServer.serverMerge(state)(leaves)(); // { accepted, root }
      console.log(
        `merge-server: merged ${leaves.length} base proofs in ${((Date.now() - t0) / 1000).toFixed(1)}s -> accepted=${result.accepted}`,
      );
      json(res, 200, { accepted: result.accepted });
    } catch (e) {
      console.error("merge-server: /merge failed:", e);
      json(res, 500, { error: String(e?.stack ?? e) });
    }
  });
});

server.on("error", (e) => {
  if (e.code === "EADDRINUSE") {
    console.error(`merge-server: port ${PORT} is already in use — stop the other server first, e.g.:\n  lsof -ti tcp:${PORT} | xargs kill -9`);
    process.exit(1);
  }
  throw e;
});

server.listen(PORT, () => {
  console.log(`merge-server: listening on http://localhost:${PORT}/  (POST /merge)`);
  console.log("merge-server: compiling circuit (one-time setup)…");
  MergeServer.initServer((st) => () => {
    state = st;
    console.log("merge-server: ready — /merge is live");
  })((msg) => () => {
    compileError = msg;
    console.error("merge-server: compile FAILED:", msg);
  })();
});
