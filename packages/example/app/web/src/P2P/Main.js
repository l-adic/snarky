// Mirror a value onto `window` (the headless harness polls window.__p2pVerified
// / __p2pPhase). Guarded so it is a no-op in any non-window context.
export const setWindowProp = (k) => (v) => () => {
  try { window[k] = v; } catch {}
};
