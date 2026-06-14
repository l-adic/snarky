import "./styles.css";
// Browser entry. The PS app is compiled by the workspace's
// purs-backend-es build into ../output-es (shared with the terminal
// package). The simulation worker is constructed HERE — vite needs the
// literal `new Worker(new URL(...))` to discover and bundle the worker
// graph — and injected into the PS entry point.
import { runApp } from "../output-es/Snarky.Example.Web.Main/index.js";

runApp(() =>
  new Worker(new URL("./worker-entry.js", import.meta.url), { type: "module" }),
)();
