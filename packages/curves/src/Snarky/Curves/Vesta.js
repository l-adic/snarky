import { createRequire } from 'module';
const require = createRequire(import.meta.url);
const napi = require('curves-napi');

export function _zero() {
    return napi.vestaScalarfieldZero();
}

export function _one() {
    return napi.vestaScalarfieldOne();
}

export function _mul(x) {
    return function(y) {
        return napi.vestaScalarfieldMul(x, y);
    };
}

export function _add(x) {
    return function(y) {
        return napi.vestaScalarfieldAdd(x, y);
    };
}

export function _sub(x) {
    return function(y) {
        return napi.vestaScalarfieldSub(x, y);
    };
}

export function _div(x) {
    return function(y) {
        return napi.vestaScalarfieldDiv(x, y);
    };
}

export function _invert(x) {
    return napi.vestaScalarfieldInvert(x);
}

export function _eq(x) {
    return function(y) {
        return napi.vestaScalarfieldEq(x, y);
    };
}

export function _toString(x) {
    return napi.vestaScalarfieldToString(x);
}

export function _rand(seed) {
    return napi.vestaScalarfieldRand(seed);
}

export function _fromBigInt(bigint) {
    return napi.vestaScalarfieldFromBigint(bigint);
}

export function _modulus() {
    return napi.vestaScalarfieldModulus();
}

export function _toBigInt(x) {
    return napi.vestaScalarfieldToBigint(x);
}

export function _pow(base) {
    return function(exponent) {
        return napi.vestaScalarfieldPow(base, exponent);
    };
}

// Base Field Operations
export function _baseFieldZero() {
    return napi.vestaBasefieldZero();
}

export function _baseFieldOne() {
    return napi.vestaBasefieldOne();
}

export function _baseFieldFromString(s) {
    return napi.vestaBasefieldFromString(s);
}

export function _baseFieldAdd(x) {
    return function(y) {
        return napi.vestaBasefieldAdd(x, y);
    };
}

export function _baseFieldSub(x) {
    return function(y) {
        return napi.vestaBasefieldSub(x, y);
    };
}

export function _baseFieldMul(x) {
    return function(y) {
        return napi.vestaBasefieldMul(x, y);
    };
}

export function _baseFieldDiv(x) {
    return function(y) {
        return napi.vestaBasefieldDiv(x, y);
    };
}

export function _baseFieldInvert(x) {
    return napi.vestaBasefieldInvert(x);
}

export function _baseFieldEq(x) {
    return function(y) {
        return napi.vestaBasefieldEq(x, y);
    };
}

export function _baseFieldToString(x) {
    return napi.vestaBasefieldToString(x);
}

export function _baseFieldRand(seed) {
    return napi.vestaBasefieldRand(seed);
}

export function _baseFieldFromBigInt(bigint) {
    return napi.vestaBasefieldFromBigint(bigint);
}

export function _baseFieldModulus() {
    return napi.vestaBasefieldModulus();
}

export function _baseFieldToBigInt(x) {
    return napi.vestaBasefieldToBigint(x);
}

export function _baseFieldPow(base) {
    return function(exponent) {
        return napi.vestaBasefieldPow(base, exponent);
    };
}

// Weierstrass Parameters
export function _weierstrassA() {
    return napi.vestaGroupWeierstrassA();
}

export function _weierstrassB() {
    return napi.vestaGroupWeierstrassB();
}

// Group Element Operations
export function _groupAdd(p1) {
    return function(p2) {
        return napi.vestaGroupAdd(p1, p2);
    };
}

export function _groupIdentity() {
    return napi.vestaGroupIdentity();
}

export function _groupRand(seed) {
    return napi.vestaGroupRand(seed);
}

export function _groupEq(p1) {
    return function(p2) {
        return napi.vestaGroupEq(p1, p2);
    };
}

export function _groupToString(p) {
    return napi.vestaGroupToString(p);
}

export function _groupNeg(p) {
    return napi.vestaGroupNeg(p);
}

export function _groupScale(scalar) {
    return function(p) {
        return napi.vestaGroupScale(p, scalar);
    };
}