// Browser prover Web Worker — the SnarkBackend pool's worker, spawned by the
// coordinator (worker-entry.js). On the init message it loads + sizes its wasm
// rayon pool FIRST, THEN imports the shared PS `buildProver` (which compiles its
// own circuit and returns a per-job prove closure); each job message is then
// decode -> prove -> encode, replied as an encoded proof string. Mirrors the
// node SnarkWorker, over a Web Worker channel.
//
// IMPORTANT ordering: kimchi-napi must be import()ed (the async wasi-browser
// loader, which pre-spawns the rayon worker pool) and initThreadPool'd BEFORE
// anything that uses it — `buildProver` pulls in the snarky-kimchi FFI which
// `require`s kimchi at module load, so it is imported LAZILY here, after init.
// Booting it eagerly (top-level import) reverses that order and hangs
// initThreadPool. Boot/phase notes are relayed to the coordinator (tag "log").

let prove = null; // (encoded WorkItem) -> encoded proof, set on init
const note = (text) => self.postMessage({ tag: "log", value: text });

self.onmessage = async (e) => {
  const m = e.data;
  try {
    if (m.tag === "init") {
      note("booting wasm kimchi");
      const kimchi = await import("kimchi-napi"); // async instantiate + pre-spawn pool
      kimchi.initThreadPool(m.threads); // wasi reports 1 cpu; size explicitly
      note(`rayon ${m.threads} threads; building SRS + compiling circuit`);
      const { buildProver } = await import("../output-es/Snarky.Example.Prover/index.js");
      prove = buildProver({ chain: m.chain, depth: m.depth })();
      note("ready");
      self.postMessage({ tag: "ready" });
    } else if (m.tag === "job") {
      const value = prove(m.value)(); // PS: (String) -> Effect String
      self.postMessage({ tag: "proof", value });
    }
  } catch (err) {
    self.postMessage({ tag: "error", value: err?.stack || String(err) });
  }
};

note("worker loaded");
