// Byte-wise equality of two Uint8Arrays (the serde blobs are typed arrays the
// napi/wasm bindings return).
export const bytesEq = (a) => (b) => {
    if (a.length !== b.length) return false;
    for (let i = 0; i < a.length; i++) {
        if (a[i] !== b[i]) return false;
    }
    return true;
};
