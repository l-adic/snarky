// Pasta projective curve arithmetic + GroupMap (Pallas).
//
// Vendored from o1js's `src/bindings/crypto/elliptic-curve.ts` (Apache-2.0,
// Copyright o1Labs). Type-stripped to plain ES module .js. We deliberately
// omit `createCurveAffine` + `PallasAffine` (they pull in the Endomorphism
// helper, not needed for our current surface — we expose `Pallas.scale`
// which already uses double-and-add, and downstream consumers can call
// `.toAffine()` when they need affine coordinates). Standalone affine
// helpers (`affineAdd`, `affineDouble`, `affineNegate`, `affineScale`,
// `affineOnCurve`) are kept so future consumers can use them without
// needing the projective curve object.
//
// Reference: original o1js source at the file path above; reference impl
// notes link to https://github.com/o1-labs/snarky/blob/78e0d952/group_map/group_map.ml
// for the GroupMap construction.

import { Fp, createField, inverse, mod, p, q, bigIntToBits } from "./PastaField.js";

// ============================================================================
// CURVE CONSTANTS (Pasta)
// ============================================================================

// y^2 = x^3 + a*x + b, Pasta uses a = 0, b = 5.
const a = 0n;
const b = 5n;

const pallasGeneratorProjective = {
  x: 1n,
  y: 12418654782883325593414442427049395787963493412651469444558597405572177144507n,
};
const vestaGeneratorProjective = {
  x: 1n,
  y: 11426906929455361843568202299992114520848200991084027513389447476559454104162n,
};

const vestaEndoBase = 2942865608506852014473558576493638302197734138389222805617480874486368177743n;
const pallasEndoBase = 20444556541222657078399132219657928148671392403212669005631716460534733845831n;
const vestaEndoScalar = 8503465768106391777493614032514048814691664078728891710322960303815233784505n;
const pallasEndoScalar = 26005156700822196841419187675678338661165322343552424574062261873906994770353n;

const projectiveZero = { x: 1n, y: 1n, z: 0n };

// ============================================================================
// PROJECTIVE ARITHMETIC (Jacobian coordinates)
// ============================================================================

function projectiveNeg({ x, y, z }, p) {
  return { x, y: y === 0n ? 0n : p - y, z };
}

function projectiveAdd(g, h, p, a) {
  if (g.z === 0n) return h;
  if (h.z === 0n) return g;
  const X1 = g.x, Y1 = g.y, Z1 = g.z;
  const X2 = h.x, Y2 = h.y, Z2 = h.z;
  // http://www.hyperelliptic.org/EFD/g1p/auto-shortw-jacobian-0.html#addition-add-2007-bl
  const Z1Z1 = mod(Z1 * Z1, p);
  const Z2Z2 = mod(Z2 * Z2, p);
  const U1 = mod(X1 * Z2Z2, p);
  const U2 = mod(X2 * Z1Z1, p);
  const S1 = mod(Y1 * Z2 * Z2Z2, p);
  const S2 = mod(Y2 * Z1 * Z1Z1, p);
  const H = mod(U2 - U1, p);
  if (H === 0n) {
    if (S1 === S2) return projectiveDouble(g, p, a);
    if (mod(S1 + S2, p) === 0n) return projectiveZero;
    throw new Error("projectiveAdd: invalid point");
  }
  const I = mod((H * H) << 2n, p);
  const J = mod(H * I, p);
  const r = 2n * (S2 - S1);
  const V = mod(U1 * I, p);
  const X3 = mod(r * r - J - 2n * V, p);
  const Y3 = mod(r * (V - X3) - 2n * S1 * J, p);
  const Z3 = mod(((Z1 + Z2) * (Z1 + Z2) - Z1Z1 - Z2Z2) * H, p);
  return { x: X3, y: Y3, z: Z3 };
}

// Specialized doubling for a = 0 (Pasta's case).
function projectiveDoubleA0(g, p) {
  if (g.z === 0n) return g;
  const X1 = g.x, Y1 = g.y, Z1 = g.z;
  if (Y1 === 0n) throw new Error("projectiveDouble: unhandled case");
  // http://www.hyperelliptic.org/EFD/g1p/auto-shortw-jacobian-0.html#doubling-dbl-2009-l
  const A = mod(X1 * X1, p);
  const B = mod(Y1 * Y1, p);
  const C = mod(B * B, p);
  const D = mod(2n * ((X1 + B) * (X1 + B) - A - C), p);
  const E = 3n * A;
  const F = mod(E * E, p);
  const X3 = mod(F - 2n * D, p);
  const Y3 = mod(E * (D - X3) - 8n * C, p);
  const Z3 = mod(2n * Y1 * Z1, p);
  return { x: X3, y: Y3, z: Z3 };
}

// Specialized doubling for a = -3.
function projectiveDoubleAminus3(g, p) {
  if (g.z === 0n) return g;
  const X1 = g.x, Y1 = g.y, Z1 = g.z;
  if (Y1 === 0n) throw new Error("projectiveDouble: unhandled case");
  const delta = mod(Z1 * Z1, p);
  const gamma = mod(Y1 * Y1, p);
  const beta = mod(X1 * gamma, p);
  let alpha = mod((X1 - delta) * (X1 + delta), p);
  alpha = alpha + alpha + alpha;
  const X3 = mod(alpha * alpha - 8n * beta, p);
  const Z3 = mod((Y1 + Z1) * (Y1 + Z1) - gamma - delta, p);
  const Y3 = mod(alpha * (4n * beta - X3) - 8n * gamma * gamma, p);
  return { x: X3, y: Y3, z: Z3 };
}

function projectiveDouble(g, p, a) {
  if (a === 0n) return projectiveDoubleA0(g, p);
  if (a + 3n === p) return projectiveDoubleAminus3(g, p);
  throw new Error(
    "Projective doubling is not implemented for general curve parameter a, only a = 0 and a = -3",
  );
}

function getProjectiveDouble(p, a) {
  if (a === 0n) return projectiveDoubleA0;
  if (a + 3n === p) return projectiveDoubleAminus3;
  throw new Error(
    "Projective doubling is not implemented for general curve parameter a, only a = 0 and a = -3",
  );
}

function projectiveSub(g, h, p, a) {
  return projectiveAdd(g, projectiveNeg(h, p), p, a);
}

function projectiveScale(g, x, p, a) {
  const double = getProjectiveDouble(p, a);
  const bits = typeof x === "bigint" ? bigIntToBits(x) : x;
  let h = projectiveZero;
  for (const bit of bits) {
    if (bit) h = projectiveAdd(h, g, p, a);
    g = double(g, p);
  }
  return h;
}

function projectiveFromAffine({ x, y, infinity }) {
  if (infinity) return projectiveZero;
  return { x, y, z: 1n };
}

function projectiveToAffine(g, p) {
  const z = g.z;
  if (z === 0n) {
    return { x: 0n, y: 0n, infinity: true };
  } else if (z === 1n) {
    return { x: g.x, y: g.y, infinity: false };
  } else {
    const zinv = inverse(z, p); // z !== 0, so inverse exists
    const zinv_squared = mod(zinv * zinv, p);
    const x = mod(g.x * zinv_squared, p);
    const y = mod(g.y * zinv * zinv_squared, p);
    return { x, y, infinity: false };
  }
}

function projectiveEqual(g, h, p) {
  // z=0 (infinity) can only equal another z=0 — guards against (0,0,0) appearing equal to any point
  if ((g.z === 0n || h.z === 0n) && g.z !== h.z) return false;
  const gz2 = mod(g.z * g.z, p);
  const hz2 = mod(h.z * h.z, p);
  if (mod(g.x * hz2 - h.x * gz2, p) !== 0n) return false;
  const gz3 = mod(gz2 * g.z, p);
  const hz3 = mod(hz2 * h.z, p);
  return mod(g.y * hz3, p) === mod(h.y * gz3, p);
}

function projectiveOnCurve({ x, y, z }, p, b, a) {
  const x3 = mod(mod(x * x, p) * x, p);
  const y2 = mod(y * y, p);
  const z2 = mod(z * z, p);
  const z4 = mod(z2 * z2, p);
  const z6 = mod(z4 * z2, p);
  return mod(y2 - x3 - a * x * z4 - b * z6, p) === 0n;
}

function projectiveInSubgroup(g, p, order, a) {
  const orderG = projectiveScale(g, order, p, a);
  return projectiveEqual(orderG, projectiveZero, p);
}

// ============================================================================
// AFFINE ARITHMETIC (standalone — not coupled to Endomorphism)
// ============================================================================

const affineZero = { x: 0n, y: 0n, infinity: true };

function affineOnCurve({ x, y, infinity }, p, a, b) {
  if (infinity) return true;
  const x2 = mod(x * x, p);
  return mod(y * y - x * x2 - a * x - b, p) === 0n;
}

function affineAdd(g, h, p, a) {
  if (g.infinity) return h;
  if (h.infinity) return g;
  const { x: x1, y: y1 } = g;
  const { x: x2, y: y2 } = h;
  if (x1 === x2) {
    if (y1 === y2) return affineDouble(g, p, a);
    return affineZero;
  }
  const d = inverse(x2 - x1, p);
  if (d === undefined) throw new Error("impossible");
  const m = mod((y2 - y1) * d, p);
  const x3 = mod(m * m - x1 - x2, p);
  const y3 = mod(m * (x1 - x3) - y1, p);
  return { x: x3, y: y3, infinity: false };
}

function affineDouble({ x, y, infinity }, p, a) {
  if (infinity) return affineZero;
  const d = inverse(2n * y, p);
  if (d === undefined) throw new Error("impossible");
  const m = mod((3n * x * x + a) * d, p);
  const x2 = mod(m * m - 2n * x, p);
  const y2 = mod(m * (x - x2) - y, p);
  return { x: x2, y: y2, infinity: false };
}

function affineNegate({ x, y, infinity }, p) {
  if (infinity) return affineZero;
  return { x, y: y === 0n ? 0n : p - y, infinity };
}

function affineScale(g, s, p, a) {
  const gProj = projectiveFromAffine(g);
  const sgProj = projectiveScale(gProj, s, p, a);
  return projectiveToAffine(sgProj, p);
}

// ============================================================================
// PROJECTIVE CURVE OBJECT
// ============================================================================

function createCurveProjective({ name, modulus, order, cofactor, generator, b, a, endoBase, endoScalar }) {
  const p_ = modulus;
  const double = getProjectiveDouble(p_, a);
  const cofactor_ = cofactor ?? 1n;
  const hasCofactor = cofactor_ !== 1n;
  return {
    name,
    modulus: p_,
    order,
    cofactor: cofactor_,
    zero: projectiveZero,
    one: { ...generator, z: 1n },
    hasEndomorphism: endoBase !== undefined && endoScalar !== undefined,
    get endoBase() {
      if (endoBase === undefined) throw new Error("`endoBase` for this curve was not provided.");
      return endoBase;
    },
    get endoScalar() {
      if (endoScalar === undefined) throw new Error("`endoScalar` for this curve was not provided.");
      return endoScalar;
    },
    a,
    b,
    hasCofactor,

    equal(g, h) {
      return projectiveEqual(g, h, p_);
    },
    isOnCurve(g) {
      return projectiveOnCurve(g, p_, b, a);
    },
    isInSubgroup(g) {
      return projectiveInSubgroup(g, p_, order, a);
    },
    add(g, h) {
      return projectiveAdd(g, h, p_, a);
    },
    double(g) {
      return double(g, p_);
    },
    negate(g) {
      return projectiveNeg(g, p_);
    },
    sub(g, h) {
      return projectiveSub(g, h, p_, a);
    },
    scale(g, s) {
      return projectiveScale(g, s, p_, a);
    },
    endomorphism({ x, y, z }) {
      if (endoBase === undefined) throw new Error("endomorphism needs `endoBase` parameter.");
      return { x: mod(endoBase * x, p_), y, z };
    },
    toAffine(g) {
      return projectiveToAffine(g, p_);
    },
    fromAffine(aff) {
      return projectiveFromAffine(aff);
    },
  };
}

const Pallas = createCurveProjective({
  name: "Pallas",
  modulus: p,
  order: q,
  generator: pallasGeneratorProjective,
  b,
  a,
  endoBase: pallasEndoBase,
  endoScalar: pallasEndoScalar,
});

const Vesta = createCurveProjective({
  name: "Vesta",
  modulus: q,
  order: p,
  generator: vestaGeneratorProjective,
  b,
  a,
  endoBase: vestaEndoBase,
  endoScalar: vestaEndoScalar,
});

// ============================================================================
// GROUP MAP (Shallue–van de Woestijne, restricted to a = 0)
// Used to deterministically map a field element to a curve point.
// Reference: https://github.com/o1-labs/snarky/blob/78e0d952/group_map/group_map.ml
// ============================================================================

const GroupMap = {
  create(F, params) {
    const { a: specA, b: specB } = params.spec;
    if (specA !== 0n) throw new Error("GroupMap only supports a = 0");

    function tryDecode(x) {
      const pow3 = F.power(x, 3n);
      const y = F.add(pow3, specB);
      if (!F.isSquare(y)) return undefined;
      return { x, y: F.sqrt(y) };
    }

    function sToVTruncated(s) {
      const { u, v, y } = s;
      return [v, F.negate(F.add(u, v)), F.add(u, F.square(y))];
    }

    function conic_to_s(c) {
      const d = F.div(c.z, c.y);
      if (d === undefined) throw new Error(`Division undefined! ${c.z}/${c.y}`);
      const v = F.sub(d, params.u_over_2);
      return { u: params.u, v, y: c.y };
    }

    function field_to_conic(t) {
      const { z: z0, y: y0 } = params.projection_point;
      const ct = F.mul(params.conic_c, t);
      const d1 = F.add(F.mul(ct, y0), z0);
      const d2 = F.add(F.mul(ct, t), 1n);
      const d = F.div(d1, d2);
      if (d === undefined) throw new Error(`Division undefined! ${d1}/${d2}`);
      const s = F.mul(2n, d);
      return { z: F.sub(z0, s), y: F.sub(y0, F.mul(s, t)) };
    }

    return {
      potentialXs: (t) => sToVTruncated(conic_to_s(field_to_conic(t))),
      tryDecode,
    };
  },
};

// Reference: https://github.com/MinaProtocol/mina/blob/af7bc892/src/lib/crypto_params/gen/gen.ml#L8-L11
const GroupMapParamsFp = {
  u: 2n,
  u_over_2: 1n,
  conic_c: 3n,
  projection_point: {
    z: 12196889842669319921865617096620076994180062626450149327690483414064673774441n,
    y: 1n,
  },
  spec: { a: 0n, b: 5n },
};

const GroupMapPallas = GroupMap.create(Fp, GroupMapParamsFp);

// IMPORTANT: this GroupMap is the SHALLUE–VAN DE WOESTIJNE construction
// used by o1js, NOT the BW19 (Brier–Walliams) construction used by our
// existing crypto-provider FFI (via `kimchi::groupmap::BWParameters`).
// Both are valid hash-to-curve maps to the same curve and produce points
// satisfying the curve equation, but for a given input `t` they produce
// *different* points (different math, different parameters). Our PS-side
// `_pallasGroupMap` / `_vestaGroupMap` FFI consumers are marked test-only
// in `Pasta.purs` (used only for testing the PS-side GroupMap impl), so
// this divergence is not load-bearing. If a future consumer needs BW19
// semantic compatibility, it'd be a separate JS impl of `BWParameters`.
//
// GroupMapVesta is not vendored yet — the `GroupMapParamsFq.projection_point`
// constants aren't in o1js (and aren't needed for the slice-3 surface).

// ============================================================================
// EXPORTS
// ============================================================================

export {
  Pallas,
  Vesta,
  GroupMap,
  GroupMapPallas,
  GroupMapParamsFp,

  pallasGeneratorProjective,
  vestaGeneratorProjective,
  pallasEndoBase,
  pallasEndoScalar,
  vestaEndoBase,
  vestaEndoScalar,

  projectiveZero,
  projectiveNeg,
  projectiveAdd,
  projectiveSub,
  projectiveDouble,
  projectiveDoubleA0,
  projectiveDoubleAminus3,
  getProjectiveDouble,
  projectiveScale,
  projectiveFromAffine,
  projectiveToAffine,
  projectiveEqual,
  projectiveOnCurve,
  projectiveInSubgroup,

  affineZero,
  affineOnCurve,
  affineAdd,
  affineDouble,
  affineNegate,
  affineScale,

  createCurveProjective,
};
