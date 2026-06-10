// Launcher for the optimized bench (`Bench.Pickles.Main`).
//
// Why a launcher and not `node -e 'import(...).then(...)'`:
// `node -e` requires a `--` separator before script args so node doesn't
// interpret `--help` / `--only` as its own options; but that `--` then
// lands in `process.argv` and trips optparse-applicative (which reads
// `--` as "end of options"). With a real `.mjs` entrypoint, node sees
// the script path and stops parsing, so `--help` / `--only X` reach
// argv cleanly without any separator.

import { main } from "./output-es/Bench.Pickles.Main/index.js";
main();
