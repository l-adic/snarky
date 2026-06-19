// IndexedDB backend for the SRS cache (see SrsCache.purs). One object store
// "srs", keyed by entryKey. Shared same-origin across the engine + self-prover
// workers.

export const _open = (name) => () =>
    new Promise((resolve, reject) => {
        const req = indexedDB.open(name, 1);
        req.onupgradeneeded = () => req.result.createObjectStore("srs");
        req.onsuccess = () => resolve(req.result);
        req.onerror = () => reject(req.error);
    });

export const _get = (db) => (key) => () =>
    new Promise((resolve, reject) => {
        const req = db.transaction("srs", "readonly").objectStore("srs").get(key);
        req.onsuccess = () => resolve(req.result ?? null); // miss → null
        req.onerror = () => reject(req.error);
    });

export const _put = (db) => (key) => (bytes) => () =>
    new Promise((resolve, reject) => {
        // Copy out of (possibly SharedArrayBuffer-backed wasm) memory into a
        // regular ArrayBuffer so IndexedDB's structured clone can store it.
        const owned = bytes.slice();
        const tx = db.transaction("srs", "readwrite");
        tx.objectStore("srs").put(owned, key);
        tx.oncomplete = () => resolve();
        tx.onerror = () => reject(tx.error);
    });
