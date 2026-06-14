// Main-thread RPC dispatcher over a prover Web Worker. Requests are
// {rpc:id, method, params}; responses are {rpc:id, ok} | {rpc:id, err}.
// Non-RPC messages (the worker's log/status events) are routed to the
// handler installed via onEvent.

export const mkClient = (worker) => () => {
  const client = { worker, pending: new Map(), nextId: 0, onEvt: null };
  worker.onmessage = (e) => {
    const m = e.data;
    if (m && typeof m.rpc === "number" && client.pending.has(m.rpc)) {
      const { resolve, reject } = client.pending.get(m.rpc);
      client.pending.delete(m.rpc);
      if ("err" in m) reject(new Error(m.err));
      else resolve(m.ok);
      return;
    }
    if (client.onEvt) client.onEvt(m);
  };
  worker.onerror = (e) => {
    if (client.onEvt) client.onEvt({ ev: "error", text: String(e?.message ?? e) });
  };
  return client;
};

export const onEvent = (client) => (handler) => () => {
  client.onEvt = (m) => handler(m)();
};

// EffectFnAff: (onError, onSuccess) => canceler
const call = (client, method, params) => (onError, onSuccess) => {
  const id = client.nextId++;
  client.pending.set(id, { resolve: onSuccess, reject: onError });
  client.worker.postMessage({ rpc: id, method, params });
  return (_c, _oce, ocs) => ocs();
};

export const _init = (client) => call(client, "init", {});
export const _seed = (client) => call(client, "seed", {});
export const _genBlock = (client) => call(client, "genBlock", {});
export const _proveLeaf = (client) => (j) => call(client, "proveLeaf", { j });
export const _merge = (client) => (params) => call(client, "merge", params);
export const _verify = (client) => (wire) => call(client, "verify", { wire });
