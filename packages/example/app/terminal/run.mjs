// Launcher for the optimized simulation (`Snarky.Example.Main`).
//
// A real .mjs entrypoint (rather than `node -e 'import(...)'`) makes node
// stop parsing options at the script path, so any future CLI args reach
// `process.argv` cleanly. Run from the REPO ROOT so the kimchi-napi node
// module resolves correctly.

import { main } from "../output-es/Snarky.Example.Main/index.js";
main();
