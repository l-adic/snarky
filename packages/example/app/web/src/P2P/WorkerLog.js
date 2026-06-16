// Forward a colog message to the worker's host as { tag:"log", value }. In a
// peer worker `self` is the worker; the host (main thread) renders it. In the
// coordinator's nested prover `self` is that worker; the coordinator relays it.
export const postLog = (m) => () => {
  self.postMessage({ tag: "log", value: m });
};
