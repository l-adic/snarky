import { createRequire } from 'module';
const require = createRequire(import.meta.url);
const napi = require('curves-napi');

// Scalar Field Operations
export function _zero() {
    return napi.pallasScalarfieldZero();
}

export function _one() {
    return napi.pallasScalarfieldOne();
}

export function _mul(x) {
    return function(y) {
        return napi.pallasScalarfieldMul(x, y);
    };
}

export function _add(x) {
    return function(y) {
        return napi.pallasScalarfieldAdd(x, y);
    };
}

export function _sub(x) {
    return function(y) {
        return napi.pallasScalarfieldSub(x, y);
    };
}

export function _div(x) {
    return function(y) {
        return napi.pallasScalarfieldDiv(x, y);
    };
}

export function _invert(x) {
    return napi.pallasScalarfieldInvert(x);
}

export function _eq(x) {
    return function(y) {
        return napi.pallasScalarfieldEq(x, y);
    };
}

export function _toString(x) {
    return napi.pallasScalarfieldToString(x);
}

export function _rand(seed) {
    return napi.pallasScalarfieldRand(seed);
}

export function _fromBigInt(bigint) {
    return napi.pallasScalarfieldFromBigint(bigint);
}

export function _modulus() {
    return napi.pallasScalarfieldModulus();
}

export function _toBigInt(x) {
    return napi.pallasScalarfieldToBigint(x);
}

export function _pow(base) {
    return function(exponent) {
        return napi.pallasScalarfieldPow(base, exponent);
    };
}

// Base Field Operations
export function _baseFieldZero() {
    return napi.pallasBasefieldZero();
}

export function _baseFieldOne() {
    return napi.pallasBasefieldOne();
}

export function _baseFieldFromString(s) {
    return napi.pallasBasefieldFromString(s);
}

export function _baseFieldAdd(x) {
    return function(y) {
        return napi.pallasBasefieldAdd(x, y);
    };
}

export function _baseFieldSub(x) {
    return function(y) {
        return napi.pallasBasefieldSub(x, y);
    };
}

export function _baseFieldMul(x) {
    return function(y) {
        return napi.pallasBasefieldMul(x, y);
    };
}

export function _baseFieldDiv(x) {
    return function(y) {
        return napi.pallasBasefieldDiv(x, y);
    };
}

export function _baseFieldInvert(x) {
    return napi.pallasBasefieldInvert(x);
}

export function _baseFieldEq(x) {
    return function(y) {
        return napi.pallasBasefieldEq(x, y);
    };
}

export function _baseFieldToString(x) {
    return napi.pallasBasefieldToString(x);
}

export function _baseFieldRand(seed) {
    return napi.pallasBasefieldRand(seed);
}

export function _baseFieldFromBigInt(bigint) {
    return napi.pallasBasefieldFromBigint(bigint);
}

export function _baseFieldModulus() {
    return napi.pallasBasefieldModulus();
}

export function _baseFieldToBigInt(x) {
    return napi.pallasBasefieldToBigint(x);
}

export function _baseFieldPow(base) {
    return function(exponent) {
        return napi.pallasBasefieldPow(base, exponent);
    };
}

// Weierstrass Parameters
export function _weierstrassA() {
    return napi.pallasGroupWeierstrassA();
}

export function _weierstrassB() {
    return napi.pallasGroupWeierstrassB();
}

// Group Element Operations
export function _groupAdd(p1) {
    return function(p2) {
        return napi.pallasGroupAdd(p1, p2);
    };
}

export function _groupIdentity() {
    return napi.pallasGroupIdentity();
}

export function _groupRand(seed) {
    return napi.pallasGroupRand(seed);
}

export function _groupEq(p1) {
    return function(p2) {
        return napi.pallasGroupEq(p1, p2);
    };
}

export function _groupToString(p) {
    return napi.pallasGroupToString(p);
}

export function _groupNeg(p) {
    return napi.pallasGroupNeg(p);
}

export function _groupScale(scalar) {
    return function(p) {
        return napi.pallasGroupScale(p, scalar);
    };
}