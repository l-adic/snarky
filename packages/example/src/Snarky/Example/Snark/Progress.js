// Thin FFI over `log-update`: in-place repaint of a multi-line block at the
// bottom of the terminal (cursor management, line clearing, and wrap handling
// all live in the library). Everything else — the tree rendering and the
// log/“sticky block” interleaving — is PureScript.

import logUpdate from "log-update";

export const repaintImpl = (s) => () => logUpdate(s);
export const clearImpl = () => logUpdate.clear();
export const doneImpl = () => logUpdate.done();
