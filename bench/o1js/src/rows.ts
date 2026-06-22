// Tuning helper: print rows per method so FILLER_ITERS can be calibrated until
// tree.step's domain log2 matches the PS workload's (2^16). Cheap — analysis
// only, no compile/prove. `npm run rows`.
export {};

import { setBackend } from "o1js";

if ((process.env.O1JS_BACKEND ?? "wasm") === "native") setBackend("native");
const { Nrr, Tree, FILLER_ITERS } = await import("./programs.js");

const log2Domain = (rows: number) => Math.ceil(Math.log2(rows));

const nrr = await Nrr.analyzeMethods();
const tree = await Tree.analyzeMethods();
console.log(`FILLER_ITERS = ${FILLER_ITERS}`);
console.log(`nrr.base   rows = ${nrr.base.rows} (domain 2^${log2Domain(nrr.base.rows)})`);
console.log(`tree.step  rows = ${tree.step.rows} (domain 2^${log2Domain(tree.step.rows)})`);
