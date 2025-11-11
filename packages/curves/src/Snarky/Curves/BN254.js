import { createRequire } from 'module';
const require = createRequire(import.meta.url);
const napi = require('curves-napi');

export function _zero() {
    return napi.bn254Zero();
}

export function _one() {
    return napi.bn254One();
}

export function _mul(x) {
    return function(y) {
        return napi.bn254Mul(x, y);
    };
}

export function _add(x) {
    return function(y) {
        return napi.bn254Add(x, y);
    };
}

export function _sub(x) {
    return function(y) {
        return napi.bn254Sub(x, y);
    };
}

export function _div(x) {
    return function(y) {
        return napi.bn254Div(x, y);
    };
}

export function _invert(x) {
    return napi.bn254Invert(x);
}

export function _eq(x) {
    return function(y) {
        return napi.bn254Eq(x, y);
    };
}

export function _toString(x) {
    return napi.bn254ToString(x);
}

export function _rand(seed) {
    return napi.bn254Rand(seed);
}

export function _fromBigInt(bigint) {
    return napi.bn254FromBigint(bigint);
}

export function _modulus() {
    return napi.bn254Modulus();
}

export function _toBigInt(x) {
    return napi.bn254ToBigint(x);
}

export function _pow(base) {
    return function(exponent) {
        return napi.bn254Pow(base, exponent);
    };
}