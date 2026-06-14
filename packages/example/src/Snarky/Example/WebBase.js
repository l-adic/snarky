// Browser base-prover hooks. The worker installs globalThis.__postLeaf /
// __postStatus / __postLog to forward to the page; _postBaseProofs POSTs the
// locally computed base proofs to the same-origin /merge endpoint.
export const postLeaf = (obj) => () => {
  if (globalThis.__postLeaf) globalThis.__postLeaf(obj);
};
export const postStatus = (s) => () => {
  if (globalThis.__postStatus) globalThis.__postStatus(s);
};
export const postLog = (obj) => () => {
  if (globalThis.__postLog) globalThis.__postLog(obj);
};

// EffectFnAff Boolean: (onError, onSuccess) => canceler
export const _postBaseProofs = (n) => (leaves) => (onError, onSuccess) => {
  (async () => {
    const r = await fetch("/merge", {
      method: "POST",
      headers: { "content-type": "application/json" },
      body: JSON.stringify({ n, leaves }),
    });
    if (r.status === 404) {
      throw new Error("POST /merge returned 404 — serve this page with merge-server.mjs (not serve.cjs)");
    }
    if (!r.ok) {
      let detail = "";
      try { detail = (await r.json()).error || ""; } catch {}
      throw new Error("merge server HTTP " + r.status + (detail ? ": " + detail : ""));
    }
    return (await r.json()).accepted;
  })().then((accepted) => onSuccess(!!accepted), onError);
  return (_c, _oce, ocs) => ocs();
};
