// Launcher for the terminal-wasm simulation (`Snarky.Example.WasmMain`):
// the SAME shared engine as the browser, over the wasm kimchi backend.
//
// Run from the REPO ROOT with KIMCHI_BACKEND=wasm (set by
// tools/run_simulation_wasm.sh) so `require('kimchi-napi')` loads the wasm
// node loader and sizes its rayon pool at require time, and srs-cache/
// resolves.
import { main } from "../output-es/Snarky.Example.WasmMain/index.js";
main();
