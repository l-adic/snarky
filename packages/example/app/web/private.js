import "./styles.css";
// Browser entry for the PRIVACY split. The PS app is compiled by the
// workspace's purs-backend-es build into ../output-es (shared with the
// full-pipeline app and the terminal package). The base-prover worker is
// constructed HERE — vite needs the literal `new Worker(new URL(...))` to
// discover and bundle the worker graph — and injected into the PS entry.
import { runApp } from "../output-es/Snarky.Example.Web.Private.Main/index.js";

runApp(() =>
  new Worker(new URL("./private-worker.js", import.meta.url), { type: "module" }),
)();
