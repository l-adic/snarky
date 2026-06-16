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

// A field element serializes as 32-byte little-endian hex (no 0x). Render it as
// a decimal string — BigInt handles any size. Reverse the byte order (LE → BE)
// first. Defensive against an unexpected shape: returns "?" rather than throwing.
export const leHexToDec = (hex) => {
  try {
    const h = (hex.startsWith("0x") ? hex.slice(2) : hex).padStart(2, "0");
    let be = "";
    for (let i = h.length - 2; i >= 0; i -= 2) be += h.slice(i, i + 2);
    return BigInt("0x" + (be || "0")).toString(10);
  } catch {
    return "?";
  }
};
