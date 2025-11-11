import { createRequire } from 'module';
const require = createRequire(import.meta.url);
const napi = require('curves-napi');

export function _zero() {
    return napi.pallasZero();
}

export function _one() {
    return napi.pallasOne();
}

export function _mul(x) {
    return function(y) {
        return napi.pallasMul(x, y);
    };
}

export function _add(x) {
    return function(y) {
        return napi.pallasAdd(x, y);
    };
}

export function _sub(x) {
    return function(y) {
        return napi.pallasSub(x, y);
    };
}

export function _div(x) {
    return function(y) {
        return napi.pallasDiv(x, y);
    };
}

export function _invert(x) {
    return napi.pallasInvert(x);
}

export function _eq(x) {
    return function(y) {
        return napi.pallasEq(x, y);
    };
}

export function _toString(x) {
    return napi.pallasToString(x);
}

export function _rand(seed) {
    return napi.pallasRand(seed);
}

export function _fromBigInt(bigint) {
    return napi.pallasFromBigint(bigint);
}

export function _modulus() {
    return napi.pallasModulus();
}

export function _toBigInt(x) {
    return napi.pallasToBigint(x);
}

export function _pow(base) {
    return function(exponent) {
        return napi.pallasPow(base, exponent);
    };
}