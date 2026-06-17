// Synchronous thread stall used for fault-injection testing of the worker
// pool's job timeout + reassignment (see SNARK_WORKER_DELAY_MS). Blocking the
// worker thread with `Atomics.wait` mimics a genuinely slow prove — the host's
// `run` doesn't return, so the pool's timer fires and the job is reassigned.
// This is the portable synchronous sleep; it's allowed off the main thread.
export const sleepSync = (ms) => () => {
  const buf = new Int32Array(new SharedArrayBuffer(4));
  Atomics.wait(buf, 0, 0, ms);
};
