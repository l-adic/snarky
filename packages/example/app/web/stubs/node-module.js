// Browser shim for node's `module` builtin: several FFI files use
// `createRequire(import.meta.url)` to load CJS deps. In the browser
// the only require target that must WORK is kimchi-napi (mapped to the
// wasm loader via the import above, which vite resolves through the
// same alias table); everything else (`fs` in Pickles.Trace, gated on
// env vars that are never set in the browser) gets a throwing proxy so
// module-level requires succeed and only actual USE fails loudly.
import * as kimchi from "kimchi-napi";

const throwing = (name) =>
  new Proxy(
    {},
    {
      get(_t, prop) {
        throw new Error(`browser shim: ${name}.${String(prop)} is node-only`);
      },
    },
  );

export const createRequire = () => (id) => {
  if (id === "kimchi-napi") return kimchi;
  return throwing(id);
};

export default { createRequire };
