import { createRequire } from 'module';
const require = createRequire(import.meta.url);
const napi = require('curves-napi');

export function _zero() {
    return napi.vestaZero();
}

export function _one() {
    return napi.vestaOne();
}

export function _mul(x) {
    return function(y) {
        return napi.vestaMul(x, y);
    };
}

export function _add(x) {
    return function(y) {
        return napi.vestaAdd(x, y);
    };
}

export function _sub(x) {
    return function(y) {
        return napi.vestaSub(x, y);
    };
}

export function _div(x) {
    return function(y) {
        return napi.vestaDiv(x, y);
    };
}

export function _invert(x) {
    return napi.vestaInvert(x);
}

export function _eq(x) {
    return function(y) {
        return napi.vestaEq(x, y);
    };
}

export function _toString(x) {
    return napi.vestaToString(x);
}

export function _rand(seed) {
    return napi.vestaRand(seed);
}

export function _fromBigInt(bigint) {
    return napi.vestaFromBigint(bigint);
}

export function _modulus() {
    return napi.vestaModulus();
}