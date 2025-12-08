import { createRequire } from 'module';
const require = createRequire(import.meta.url);
const napi = require('snarky-crypto');

// Scalar Field Operations
export function _zero() {
    return napi.bn254ScalarfieldZero();
}

export function _one() {
    return napi.bn254ScalarfieldOne();
}

export function _mul(x) {
    return function(y) {
        return napi.bn254ScalarfieldMul(x, y);
    };
}

export function _add(x) {
    return function(y) {
        return napi.bn254ScalarfieldAdd(x, y);
    };
}

export function _sub(x) {
    return function(y) {
        return napi.bn254ScalarfieldSub(x, y);
    };
}

export function _div(x) {
    return function(y) {
        return napi.bn254ScalarfieldDiv(x, y);
    };
}

export function _invert(x) {
    return napi.bn254ScalarfieldInvert(x);
}

export function _eq(x) {
    return function(y) {
        return napi.bn254ScalarfieldEq(x, y);
    };
}

export function _toString(x) {
    return napi.bn254ScalarfieldToString(x);
}

export function _rand(seed) {
    return napi.bn254ScalarfieldRand(seed);
}

export function _fromBigInt(bigint) {
    return napi.bn254ScalarfieldFromBigint(bigint);
}

export function _modulus() {
    return napi.bn254ScalarfieldModulus();
}

export function _toBigInt(x) {
    return napi.bn254ScalarfieldToBigint(x);
}

export function _pow(base) {
    return function(exponent) {
        return napi.bn254ScalarfieldPow(base, exponent);
    };
}

// Base Field Operations
export function _baseFieldZero() {
    return napi.bn254BasefieldZero();
}

export function _baseFieldOne() {
    return napi.bn254BasefieldOne();
}

export function _baseFieldFromString(s) {
    return napi.bn254BasefieldFromString(s);
}

export function _baseFieldAdd(x) {
    return function(y) {
        return napi.bn254BasefieldAdd(x, y);
    };
}

export function _baseFieldSub(x) {
    return function(y) {
        return napi.bn254BasefieldSub(x, y);
    };
}

export function _baseFieldMul(x) {
    return function(y) {
        return napi.bn254BasefieldMul(x, y);
    };
}

export function _baseFieldDiv(x) {
    return function(y) {
        return napi.bn254BasefieldDiv(x, y);
    };
}

export function _baseFieldInvert(x) {
    return napi.bn254BasefieldInvert(x);
}

export function _baseFieldEq(x) {
    return function(y) {
        return napi.bn254BasefieldEq(x, y);
    };
}

export function _baseFieldToString(x) {
    return napi.bn254BasefieldToString(x);
}

export function _baseFieldRand(seed) {
    return napi.bn254BasefieldRand(seed);
}

export function _baseFieldFromBigInt(bigint) {
    return napi.bn254BasefieldFromBigint(bigint);
}

export function _baseFieldModulus() {
    return napi.bn254BasefieldModulus();
}

export function _baseFieldToBigInt(x) {
    return napi.bn254BasefieldToBigint(x);
}

export function _baseFieldPow(base) {
    return function(exponent) {
        return napi.bn254BasefieldPow(base, exponent);
    };
}

// Weierstrass Parameters
export function _weierstrassA() {
    return napi.bn254GroupWeierstrassA();
}

export function _weierstrassB() {
    return napi.bn254GroupWeierstrassB();
}

// Group Element Operations
export function _groupAdd(p1) {
    return function(p2) {
        return napi.bn254GroupAdd(p1, p2);
    };
}

export function _groupIdentity() {
    return napi.bn254GroupIdentity();
}

export function _groupRand(seed) {
    return napi.bn254GroupRand(seed);
}

export function _groupEq(p1) {
    return function(p2) {
        return napi.bn254GroupEq(p1, p2);
    };
}

export function _groupToString(p) {
    return napi.bn254GroupToString(p);
}

export function _groupNeg(p) {
    return napi.bn254GroupNeg(p);
}

export function _groupScale(scalar) {
    return function(p) {
        return napi.bn254GroupScale(p, scalar);
    };
}

export function _toAffine(just, nothing, value) {
  let p = napi.bn254GroupToAffine(value)
  if (p == null) {
    return nothing;
  } else {
    return just([p[0], p[1]]);
  }
}