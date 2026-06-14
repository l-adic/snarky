// IndexedDB proof cache keyed by stmtKey → proof wire. No-op where IndexedDB
// is absent (e.g. some headless/worker contexts).
const DB = "snarky-p2p-proofs";
const hasIDB = () => typeof indexedDB !== "undefined";

function openDB() {
  return new Promise((res, rej) => {
    const r = indexedDB.open(DB, 1);
    r.onupgradeneeded = () => r.result.createObjectStore("proofs");
    r.onsuccess = () => res(r.result);
    r.onerror = () => rej(r.error);
  });
}

export const cachePut = (key) => (wire) => () => {
  if (!hasIDB()) return;
  (async () => {
    try {
      const db = await openDB();
      const tx = db.transaction("proofs", "readwrite");
      tx.objectStore("proofs").put(wire, key);
    } catch {}
  })();
};

// EffectFnAff (Array { key, wire })
export const _cacheAll = (onError, onSuccess) => {
  (async () => {
    if (!hasIDB()) return [];
    const db = await openDB();
    const store = db.transaction("proofs", "readonly").objectStore("proofs");
    const keys = await new Promise((res, rej) => { const q = store.getAllKeys(); q.onsuccess = () => res(q.result); q.onerror = () => rej(q.error); });
    const vals = await new Promise((res, rej) => { const q = store.getAll(); q.onsuccess = () => res(q.result); q.onerror = () => rej(q.error); });
    return keys.map((k, i) => ({ key: String(k), wire: vals[i] }));
  })().then(onSuccess, (e) => { try { onSuccess([]); } catch { onError(e); } });
  return (_c, _oce, ocs) => ocs();
};
