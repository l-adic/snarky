// IndexedDB backend for the Lagrange cache (see Idb.purs). One object store
// "bases", keyed by keyString. Shared same-origin across the engine + self-prover
// workers.

export const _open = (name) => () =>
    new Promise((resolve, reject) => {
        const req = indexedDB.open(name, 1);
        req.onupgradeneeded = () => req.result.createObjectStore("bases");
        req.onsuccess = () => resolve(req.result);
        req.onerror = () => reject(req.error);
    });

export const _put = (db) => (key) => (bytes) => () =>
    new Promise((resolve, reject) => {
        // Copy out of (possibly SharedArrayBuffer-backed wasm) memory into a
        // regular ArrayBuffer so IndexedDB's structured clone can store it.
        const owned = bytes.slice();
        const tx = db.transaction("bases", "readwrite");
        tx.objectStore("bases").put(owned, key);
        tx.oncomplete = () => resolve();
        tx.onerror = () => reject(tx.error);
    });

// Bulk-load every stored entry to hydrate the in-memory map. Keys and values
// come back in the same order; resolve once both requests succeed.
export const _getAll = (db) => () =>
    new Promise((resolve, reject) => {
        const store = db.transaction("bases", "readonly").objectStore("bases");
        const valsReq = store.getAll();
        const keysReq = store.getAllKeys();
        let keys, values;
        const done = () => {
            if (keys !== undefined && values !== undefined) resolve({ keys, values });
        };
        valsReq.onsuccess = () => {
            values = valsReq.result;
            done();
        };
        keysReq.onsuccess = () => {
            keys = keysReq.result;
            done();
        };
        valsReq.onerror = () => reject(valsReq.error);
        keysReq.onerror = () => reject(keysReq.error);
    });
