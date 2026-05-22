// Pure-JS Pasta finite-field arithmetic.
//
// The algorithms (mod / power / inverse / sqrt / isSquare) and the Pasta
// prime constants are vendored from o1js's `src/bindings/crypto/finite-field.ts`
// (Apache-2.0, Copyright o1Labs). Type-stripped to plain ES module .js.
// Trimmed to what we need at the FFI boundary: field arithmetic + canonical
// 32-byte LE encoding + sqrt/isSquare/bigIntToBits used by `PastaCurve.js`.
//
// Boundary contract: a field element on the JS side IS a `bigint` reduced
// to `[0, p)`. There is no class wrapper, no External handle — equality is
// `===`, hashing/serialization is the canonical integer.
//
// The constants are hardcoded BigInt literals (matching o1js); the parity
// harness in `test/parity-harness.mjs` asserts at load time that they equal
// what the existing FFI's `*ScalarfieldModulus()` returns.

// ============================================================================
// PASTA PRIMES + TWO-ADICITY CONSTANTS (needed for sqrt)
// ============================================================================

// p — Pallas base field / Vesta scalar field. Matches o1js's `Fp` modulus.
const P = 0x40000000000000000000000000000000224698fc094cf91b992d30ed00000001n;
// q — Pallas scalar field / Vesta base field. Matches o1js's `Fq` modulus.
const Q = 0x40000000000000000000000000000000224698fc0994a8dd8c46eb2100000001n;

// p - 1 = 2^32 * t, with t odd
const P_MINUS_ONE_ODD_FACTOR = 0x40000000000000000000000000000000224698fc094cf91b992d30edn;
const Q_MINUS_ONE_ODD_FACTOR = 0x40000000000000000000000000000000224698fc0994a8dd8c46eb21n;

// primitive 2^32-th roots of unity (5^t mod p, since 5 generates the
// multiplicative group of both Pasta primes)
const TWOADIC_ROOT_FP = 0x2bce74deac30ebda362120830561f81aea322bf2b7bb7584bdad6fabd87ea32fn;
const TWOADIC_ROOT_FQ = 0x2de6a9b8746d3f589e5c4dfd492ae26e9bb97ea3c106f049a70e2c1102b6d05fn;

const TWOADICITY = 32n; // same for both Pasta primes

// ============================================================================
// GENERIC FINITE-FIELD ALGORITHMS over BigInt
// ============================================================================

function mod(x, p) {
  let r = x % p;
  return r < 0n ? r + p : r;
}

function power(a, n, p) {
  a = mod(a, p);
  let x = 1n;
  let exp = n;
  while (exp > 0n) {
    if (exp & 1n) x = mod(x * a, p);
    a = mod(a * a, p);
    exp >>= 1n;
  }
  return x;
}

// Extended Euclidean inverse. Returns undefined if a ≡ 0 mod p.
function inverse(a, p) {
  a = mod(a, p);
  if (a === 0n) return undefined;
  let b = p;
  let x = 0n,
    y = 1n,
    u = 1n,
    v = 0n;
  while (a !== 0n) {
    const q = b / a;
    const r = mod(b, a);
    const m = x - u * q;
    const n = y - v * q;
    b = a;
    a = r;
    x = u;
    y = v;
    u = m;
    v = n;
  }
  if (b !== 1n) return undefined;
  return mod(x, p);
}

// Tonelli-Shanks square root. `Q` is the odd factor (p-1 = 2^M * Q),
// `c` a known primitive 2^M-th root of unity, `M` the two-adicity.
function sqrt(n_, p, Q, c, M) {
  let n = mod(n_, p);
  if (n === 0n) return 0n;
  let t = power(n, (Q - 1n) >> 1n, p);
  let R = mod(t * n, p);
  t = mod(t * R, p);
  while (true) {
    if (t === 1n) return R;
    let i = 0n;
    let s = t;
    while (s !== 1n) {
      s = mod(s * s, p);
      i = i + 1n;
    }
    if (i === M) return undefined; // not a square
    let b = power(c, 1n << (M - i - 1n), p);
    M = i;
    c = mod(b * b, p);
    t = mod(t * c, p);
    R = mod(R * b, p);
  }
}

function isSquare(x_, p) {
  const x = mod(x_, p);
  if (x === 0n) return true;
  // Euler's criterion: x is a square iff x^((p-1)/2) ≡ 1 (mod p)
  return power(x, (p - 1n) / 2n, p) === 1n;
}

// ============================================================================
// CANONICAL 32-BYTE LITTLE-ENDIAN ENCODING + BIT HELPERS
// ============================================================================

const MASK64 = (1n << 64n) - 1n;

function bigintToBytes32LE(x) {
  const bytes = new Uint8Array(32);
  const view = new DataView(bytes.buffer);
  view.setBigUint64(0, x & MASK64, true);
  view.setBigUint64(8, (x >> 64n) & MASK64, true);
  view.setBigUint64(16, (x >> 128n) & MASK64, true);
  view.setBigUint64(24, x >> 192n, true);
  return bytes;
}

function bytes32LEToBigint(bytes) {
  if (bytes.byteLength !== 32) {
    throw new Error(`bytes32LEToBigint: expected 32 bytes, got ${bytes.byteLength}`);
  }
  const view = new DataView(bytes.buffer, bytes.byteOffset, bytes.byteLength);
  return (
    view.getBigUint64(0, true) |
    (view.getBigUint64(8, true) << 64n) |
    (view.getBigUint64(16, true) << 128n) |
    (view.getBigUint64(24, true) << 192n)
  );
}

function bytesToHex(bytes) {
  let s = "";
  for (let i = 0; i < bytes.length; i++) {
    s += bytes[i].toString(16).padStart(2, "0");
  }
  return s;
}

function hexToBytes(hex) {
  if (hex.length % 2 !== 0) throw new Error(`hexToBytes: odd-length hex string`);
  const bytes = new Uint8Array(hex.length / 2);
  for (let i = 0; i < bytes.length; i++) {
    bytes[i] = parseInt(hex.substr(i * 2, 2), 16);
  }
  return bytes;
}

function bigintToHexLE32(x) {
  return bytesToHex(bigintToBytes32LE(x));
}

function hexLE32ToBigint(hex) {
  return bytes32LEToBigint(hexToBytes(hex));
}

// Bit-decomposition (low bit first), used by curve scalar mul. Always
// produces enough bits to represent `x`; trailing zeros are omitted.
function bigIntToBits(x) {
  const bits = [];
  for (; x > 0n; x >>= 1n) bits.push((x & 1n) === 1n);
  return bits;
}

// ============================================================================
// FIELD CONSTRUCTOR
// Mirrors the shape of o1js's `createField` return so vendored consumers
// (PastaCurve.js, vendored Poseidon, …) can call `F.add`, `F.sqrt`, etc.
// ============================================================================

function createField(p, constants) {
  // `constants` carries the sqrt parameters (oddFactor t, twoadicRoot c,
  // twoadicity M). Required to use F.sqrt and F.isSquare.
  const oddFactor = constants?.oddFactor;
  const twoadicRoot = constants?.twoadicRoot;
  const twoadicity = constants?.twoadicity;

  return {
    modulus: p,
    t: oddFactor,
    M: twoadicity,
    twoadicRoot,

    mod(x) {
      return mod(x, p);
    },
    add(x, y) {
      return mod(x + y, p);
    },
    sub(x, y) {
      return mod(x - y, p);
    },
    negate(x) {
      return x === 0n ? 0n : mod(-x, p);
    },
    mul(x, y) {
      return mod(x * y, p);
    },
    square(x) {
      return mod(x * x, p);
    },
    // Dot product of two equal-length BigInt vectors mod p (used by the MDS
    // multiply in vendored Poseidon).
    dot(xs, ys) {
      let z = 0n;
      const n = xs.length;
      for (let i = 0; i < n; i++) {
        z += xs[i] * ys[i];
      }
      return mod(z, p);
    },
    inverse(x) {
      return inverse(x, p);
    },
    div(x, y) {
      const yinv = inverse(y, p);
      if (yinv === undefined) return undefined;
      return mod(x * yinv, p);
    },
    power(x, n) {
      return power(x, n, p);
    },
    sqrt(x) {
      if (oddFactor === undefined || twoadicRoot === undefined || twoadicity === undefined) {
        throw new Error("sqrt: field constructed without two-adicity constants");
      }
      return sqrt(x, p, oddFactor, twoadicRoot, twoadicity);
    },
    isSquare(x) {
      return isSquare(x, p);
    },
    equal(x, y) {
      const xc = x >= 0n && x < p ? x : mod(x, p);
      const yc = y >= 0n && y < p ? y : mod(y, p);
      return xc === yc;
    },

    fromBigint(x) {
      return mod(x, p);
    },
    toBigint(x) {
      return x;
    },
    toBytesLE(x) {
      return bigintToBytes32LE(x);
    },
    fromBytesLE(bytes) {
      return bytes32LEToBigint(bytes);
    },
    toHexLE(x) {
      return bigintToHexLE32(x);
    },
    fromHexLE(hex) {
      return hexLE32ToBigint(hex);
    },
  };
}

// ============================================================================
// PASTA SPECIALIZATIONS + o1js-COMPATIBLE ALIASES
//
// Naming under our PS convention:
//   PallasScalar : Pallas's scalar field = Fq = modulus Q
//   PallasBase   : Pallas's base field   = Fp = modulus P  (= Vesta scalar)
//   VestaScalar  : Vesta's scalar field  = Fp = modulus P  (alias of PallasBase)
//   VestaBase    : Vesta's base field    = Fq = modulus Q  (alias of PallasScalar)
//
// o1js calls these `Fp` (modulus P) and `Fq` (modulus Q). Aliases are
// exported below so the vendored o1js files (PastaCurve.js, …) can
// `import { Fp, Fq, p, q } from './PastaField.js'` unchanged.
// ============================================================================

const Fp = createField(P, {
  oddFactor: P_MINUS_ONE_ODD_FACTOR,
  twoadicRoot: TWOADIC_ROOT_FP,
  twoadicity: TWOADICITY,
});
const Fq = createField(Q, {
  oddFactor: Q_MINUS_ONE_ODD_FACTOR,
  twoadicRoot: TWOADIC_ROOT_FQ,
  twoadicity: TWOADICITY,
});

const PallasBase = Fp;
const VestaScalar = Fp;
const PallasScalar = Fq;
const VestaBase = Fq;

// Lower-case modulus aliases (match o1js naming in vendored files).
const p = P;
const q = Q;

export {
  // Pasta primes + two-adicity (uppercase + o1js-style lowercase aliases)
  P,
  Q,
  p,
  q,
  P_MINUS_ONE_ODD_FACTOR,
  Q_MINUS_ONE_ODD_FACTOR,
  TWOADIC_ROOT_FP,
  TWOADIC_ROOT_FQ,
  TWOADICITY,

  // Generic algorithms
  mod,
  power,
  inverse,
  sqrt,
  isSquare,

  // Codec + helpers
  bigintToBytes32LE,
  bytes32LEToBigint,
  bigintToHexLE32,
  hexLE32ToBigint,
  bigIntToBits,

  // Field constructor
  createField,

  // Pasta-specialized fields (both our names and o1js's aliases)
  Fp,
  Fq,
  PallasScalar,
  PallasBase,
  VestaScalar,
  VestaBase,
};
