// Launcher for the optimized bench (`Bench.Pickles.Main`).
//
// Why a launcher and not `node -e 'import(...).then(...)'`:
// `node -e` requires a `--` separator before script args so node doesn't
// interpret `--help` / `--only` as its own options; but that `--` then
// lands in `process.argv` and trips optparse-applicative (which reads
// `--` as "end of options"). With a real `.mjs` entrypoint, node sees
// the script path and stops parsing, so `--help` / `--only X` reach
// argv cleanly without any separator.
//
// --wasm: select the kimchi-napi wasm backend. Must be handled HERE (before
// any import touches kimchi-napi) because kimchi-napi/index.js reads
// KIMCHI_BACKEND at require-time. Stripped from argv so Options.Applicative
// in the PureScript main doesn't see it.

const wasmIdx = process.argv.indexOf("--wasm");
if (wasmIdx >= 0) {
  process.argv.splice(wasmIdx, 1);
  process.env.KIMCHI_BACKEND = "wasm";
}

// Dynamic import so KIMCHI_BACKEND is set before kimchi-napi loads.
const { main } = await import("./output-es/Bench.Pickles.Main/index.js");
main();
