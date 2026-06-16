// Re-run `eff` every `ms` until `stop` returns true or `maxTimes` runs are made,
// then stop. Used to re-announce `Join` periodically: a single announce can be
// lost over WebRTC (the first one may race the data channel opening, or the
// coordinator may still be discovering us), so a worker that joined an
// already-running session would otherwise sit silently unused. BroadcastChannel
// masks this with repeated presence beats; this gives the same robustness to any
// transport. Stops as soon as the coordinator assigns a job (it plainly knows us
// then), or after a bounded number of tries (so a worker in an empty room — no
// coordinator yet — doesn't spam the relay forever; a coordinator that appears
// later is still picked up via the onPeer re-announce).
export const reannounce = (ms) => (maxTimes) => (stop) => (eff) => () => {
  let n = 0;
  const h = setInterval(() => {
    if (stop() || n >= maxTimes) {
      clearInterval(h);
      return;
    }
    n += 1;
    eff();
  }, ms);
};
