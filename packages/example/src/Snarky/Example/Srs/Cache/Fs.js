// Node filesystem backend for the SRS cache (see Fs.purs). One file per entry.
import { readFile, writeFile, mkdir } from "node:fs/promises";
import { join } from "node:path";

export const _get = (dir) => (key) => () =>
    readFile(join(dir, key)).then(
        (buf) => buf, // a Buffer is a Uint8Array; napi accepts it directly
        (err) => {
            if (err && err.code === "ENOENT") return null; // miss
            throw err;
        },
    );

export const _put = (dir) => (key) => (bytes) => () =>
    mkdir(dir, { recursive: true }).then(() => writeFile(join(dir, key), bytes));
