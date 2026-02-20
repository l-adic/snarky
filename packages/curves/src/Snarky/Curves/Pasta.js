import { createRequire } from 'module';
const require = createRequire(import.meta.url);
const napi = require('snarky-crypto');

// ============================================================================
// PALLAS CURVE FUNCTIONS
// ============================================================================

// Pallas Scalar Field Operations
export function _pallasZero() {
    return napi.pallasScalarfieldZero();
}

export function _pallasOne() {
    return napi.pallasScalarfieldOne();
}

export function _pallasMul(x) {
    return function(y) {
        return napi.pallasScalarfieldMul(x, y);
    };
}

export function _pallasAdd(x) {
    return function(y) {
        return napi.pallasScalarfieldAdd(x, y);
    };
}

export function _pallasSub(x) {
    return function(y) {
        return napi.pallasScalarfieldSub(x, y);
    };
}

export function _pallasDiv(x) {
    return function(y) {
        return napi.pallasScalarfieldDiv(x, y);
    };
}

export function _pallasInvert(x) {
    return napi.pallasScalarfieldInvert(x);
}

export function _pallasEq(x) {
    return function(y) {
        return napi.pallasScalarfieldEq(x, y);
    };
}

export function _pallasToString(x) {
    return napi.pallasScalarfieldToString(x);
}

export function _pallasRand(seed) {
    return napi.pallasScalarfieldRand(seed);
}

export function _pallasFromBigInt(bigint) {
    return napi.pallasScalarfieldFromBigint(bigint);
}

export function _pallasModulus() {
    return BigInt(napi.pallasScalarfieldModulus());
}

export function _pallasToBigInt(x) {
    return napi.pallasScalarfieldToBigint(x);
}

export function _pallasPow(base) {
    return function(exponent) {
        return napi.pallasScalarfieldPow(base, exponent);
    };
}

export function _pallasScalarFieldFromHexLe(hex) {
    return napi.pallasScalarfieldFromHexLe(hex);
}

export function _pallasScalarFieldToHexLe(x) {
    return napi.pallasScalarfieldToHexLe(x);
}

// Note: Pallas base field functions removed - now handled via VestaScalarField type alias

// Pallas Weierstrass Parameters (Pallas curve coefficients in Pallas base field)
export function _pallasWeierstrassA() {
    return napi.pallasGroupWeierstrassA();
}

export function _pallasWeierstrassB() {
    return napi.pallasGroupWeierstrassB();
}

// Pallas Group Element Operations
export function _pallasGroupAdd(p1) {
    return function(p2) {
        return napi.pallasGroupAdd(p1, p2);
    };
}

export function _pallasGroupIdentity() {
    return napi.pallasGroupIdentity();
}

export function _pallasGroupGenerator() {
    return napi.pallasGroupGenerator();
}

export function _pallasGroupRand(seed) {
    return napi.pallasGroupRand(seed);
}

export function _pallasGroupEq(p1) {
    return function(p2) {
        return napi.pallasGroupEq(p1, p2);
    };
}

export function _pallasGroupToString(p) {
    return napi.pallasGroupToString(p);
}

export function _pallasGroupNeg(p) {
    return napi.pallasGroupNeg(p);
}

export function _pallasGroupScale(scalar) {
    return function(p) {
        return napi.pallasGroupScale(p, scalar);
    };
}

export function _pallasToAffine(just, nothing, value) {
  var p = napi.pallasGroupToAffine(value);
  if (p == null) {
    return nothing;
  } else {
    return just([p[0], p[1]]);
  }
}

// ============================================================================
// VESTA CURVE FUNCTIONS
// ============================================================================

// Vesta Scalar Field Operations
export function _vestaScalarFieldZero() {
    return napi.vestaScalarfieldZero();
}

export function _vestaScalarFieldOne() {
    return napi.vestaScalarfieldOne();
}

export function _vestaScalarFieldAdd(a) {
    return function(b) {
        return napi.vestaScalarfieldAdd(a, b);
    };
}

export function _vestaScalarFieldMul(a) {
    return function(b) {
        return napi.vestaScalarfieldMul(a, b);
    };
}

export function _vestaScalarFieldSub(a) {
    return function(b) {
        return napi.vestaScalarfieldSub(a, b);
    };
}

export function _vestaScalarFieldDiv(a) {
    return function(b) {
        return napi.vestaScalarfieldDiv(a, b);
    };
}

export function _vestaScalarFieldInvert(a) {
    return napi.vestaScalarfieldInvert(a);
}

export function _vestaScalarFieldEq(a) {
    return function(b) {
        return napi.vestaScalarfieldEq(a, b);
    };
}

export function _vestaScalarFieldToString(a) {
    return napi.vestaScalarfieldToString(a);
}

export function _vestaScalarFieldRand(seed) {
    return napi.vestaScalarfieldRand(seed);
}

export function _vestaScalarFieldFromBigInt(bigint) {
    return napi.vestaScalarfieldFromBigint(bigint);
}

export function _vestaScalarFieldToBigInt(field) {
    return napi.vestaScalarfieldToBigint(field);
}

export function _vestaScalarFieldPow(base) {
    return function(exponent) {
        return napi.vestaScalarfieldPow(base, exponent);
    };
}

export function _vestaScalarFieldModulus() {
    return BigInt(napi.vestaScalarfieldModulus());
}

export function _vestaScalarFieldFromHexLe(hex) {
    return napi.vestaScalarfieldFromHexLe(hex);
}

export function _vestaScalarFieldToHexLe(x) {
    return napi.vestaScalarfieldToHexLe(x);
}

// Note: Vesta base field functions removed - now handled via PallasScalarField type alias

// Vesta Weierstrass Parameters
export function _vestaWeierstrassA() {
    return napi.vestaGroupWeierstrassA();
}

export function _vestaWeierstrassB() {
    return napi.vestaGroupWeierstrassB();
}

// Vesta Group Element Operations
export function _vestaGroupAdd(p1) {
    return function(p2) {
        return napi.vestaGroupAdd(p1, p2);
    };
}

export function _vestaGroupIdentity() {
    return napi.vestaGroupIdentity();
}

export function _vestaGroupGenerator() {
    return napi.vestaGroupGenerator();
}

export function _vestaGroupRand(seed) {
    return napi.vestaGroupRand(seed);
}

export function _vestaGroupEq(p1) {
    return function(p2) {
        return napi.vestaGroupEq(p1, p2);
    };
}

export function _vestaGroupToString(p) {
    return napi.vestaGroupToString(p);
}

export function _vestaGroupNeg(p) {
    return napi.vestaGroupNeg(p);
}

export function _vestaGroupScale(scalar) {
    return function(p) {
        return napi.vestaGroupScale(p, scalar);
    };
}

export function _vestaToAffine(just, nothing, value) {
  let p = napi.vestaGroupToAffine(value)
  if (p == null) {
    return nothing;
  } else {
    return just([p[0], p[1]]);
  }
}

export function _vestaFromAffine({x,y}) {
    return napi.vestaGroupFromAffine(x,y)
}

export function _pallasFromAffine({x,y}) {
    return napi.pallasGroupFromAffine(x,y)
}

// Endomorphism coefficients
export function _pallasEndoBase() {
    return napi.pallasEndoBase();
}

export function _pallasEndoScalar() {
    return napi.pallasEndoScalar();
}

export function _vestaEndoBase() {
    return napi.vestaEndoBase();
}

export function _vestaEndoScalar() {
    return napi.vestaEndoScalar();
}

// Square root and quadratic residue functions
export function _pallasIsSquare(x) {
    return napi.pallasScalarfieldIsSquare(x);
}

export function _pallasSqrt(just) {
    return function(nothing) {
        return function(x) {
            const result = napi.pallasScalarfieldSqrt(x);
            if (result == null) {
                return nothing;
            } else {
                return just(result);
            }
        };
    };
}

export function _vestaScalarFieldIsSquare(x) {
    return napi.vestaScalarfieldIsSquare(x);
}

export function _vestaScalarFieldSqrt(just) {
    return function(nothing) {
        return function(x) {
            const result = napi.vestaScalarfieldSqrt(x);
            if (result == null) {
                return nothing;
            } else {
                return just(result);
            }
        };
    };
}

// BW19 GroupMap parameters
// Returns array: [u, fu, sqrtNeg3U2MinusUOver2, sqrtNeg3U2, inv3U2]
export function _pallasBW19Params() {
    return napi.pallasBw19Params();
}

export function _vestaBW19Params() {
    return napi.vestaBw19Params();
}

// Group map (hash-to-curve) functions
export function _pallasGroupMap(t) {
    return napi.pallasGroupMap(t);
}

export function _vestaGroupMap(t) {
    return napi.vestaGroupMap(t);
}