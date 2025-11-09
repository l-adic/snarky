import { createRequire } from 'module';
const require = createRequire(import.meta.url);
const napi = require('curves-napi');

export function zero() {
    return napi.pallasZero();
}

export function one() {
    return napi.pallasOne();
}

export function mul(x) {
    return function(y) {
        return napi.pallasMul(x, y);
    };
}

export function add(x) {
    return function(y) {
        return napi.pallasAdd(x, y);
    };
}

export function sub(x) {
    return function(y) {
        return napi.pallasSub(x, y);
    };
}

export function div(x) {
    return function(y) {
        return napi.pallasDiv(x, y);
    };
}

export function invert(x) {
    return napi.pallasInvert(x);
}

export function eq(x) {
    return function(y) {
        return napi.pallasEq(x, y);
    };
}

export function toString(x) {
    return napi.pallasToString(x);
}

export function rand(seed) {
    return napi.pallasRand(seed);
}

export function fromBigInt(bigint) {
    return napi.pallasFromBigint(bigint);
}

export function modulus() {
    return napi.pallasModulus();
}