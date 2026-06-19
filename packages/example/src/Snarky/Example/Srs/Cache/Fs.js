// Node filesystem backend for the SRS cache (see Fs.purs). One file per entry.
import { readFile, writeFile, mkdir, rename } from "node:fs/promises";
import { join } from "node:path";
import { randomUUID } from "node:crypto";

export const _get = (dir) => (key) => () =>
    readFile(join(dir, key)).then(
        (buf) => buf, // a Buffer is a Uint8Array; napi accepts it directly
        (err) => {
            if (err && err.code === "ENOENT") return null; // miss
            throw err;
        },
    );

// Atomic write: many worker threads may cold-build the same entry at once.
// Write to a unique temp file then rename (atomic on POSIX, same dir = same FS),
// so a concurrent reader never sees a half-written blob and concurrent writers
// can't interleave. The bytes are deterministic, so last-writer-wins is safe.
export const _put = (dir) => (key) => (bytes) => () =>
    mkdir(dir, { recursive: true }).then(() => {
        const tmp = join(dir, `.${key}.${randomUUID()}.tmp`);
        return writeFile(tmp, bytes).then(() => rename(tmp, join(dir, key)));
    });
