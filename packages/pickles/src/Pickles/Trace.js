// FFI for Pickles.Trace.
//
// Sister to mina/src/lib/crypto/pickles/pickles_trace.ml. Both write to the
// file named by the PICKLES_TRACE_FILE env var, one line per traced value,
// in the format `[LABEL] DECIMAL_VALUE\n`. The two trace files are then
// diffed to verify byte-identical pickles transcript reproduction.
//
// The file handle is opened lazily on first call (truncating any existing
// contents — each test run starts fresh) and kept open for the lifetime of
// the Node process. When PICKLES_TRACE_FILE is unset, every call is a no-op.

import { createRequire } from 'module';
const require = createRequire(import.meta.url);
const fs = require('fs');

const ENV_VAR = 'PICKLES_TRACE_FILE';

let initialized = false;
let traceFd = null;

function getFd() {
  if (initialized) return traceFd;
  initialized = true;
  const path = process.env[ENV_VAR];
  if (path === undefined || path === null || path === '') {
    traceFd = null;
    return null;
  }
  // Truncating mode: each test run starts with an empty trace file.
  traceFd = fs.openSync(path, 'w');
  return traceFd;
}

export const emitLineImpl = (label) => (valueStr) => () => {
  const fd = getFd();
  if (fd === null) return;
  // One write call per line; fs.writeSync flushes through to the OS,
  // matching the OCaml side's Out_channel.flush after each emit.
  fs.writeSync(fd, '[' + label + '] ' + valueStr + '\n');
};
