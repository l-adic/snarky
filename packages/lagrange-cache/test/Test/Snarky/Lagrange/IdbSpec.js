import "fake-indexeddb/auto";

export const installFakeIndexedDb = () => {};

export const mkBytes = (n) => {
    const a = new Uint8Array(n);
    for (let i = 0; i < n; i++) a[i] = i;
    return a;
};

export const bytesLen = (a) => a.length;
