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
