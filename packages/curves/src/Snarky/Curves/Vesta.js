import { createRequire } from 'module';
const require = createRequire(import.meta.url);
const napi = require('curves-napi');

export function zero() {
    return napi.vestaZero();
}

export function one() {
    return napi.vestaOne();
}

export function mul(x) {
    return function(y) {
        return napi.vestaMul(x, y);
    };
}

export function add(x) {
    return function(y) {
        return napi.vestaAdd(x, y);
    };
}

export function sub(x) {
    return function(y) {
        return napi.vestaSub(x, y);
    };
}

export function div(x) {
    return function(y) {
        return napi.vestaDiv(x, y);
    };
}

export function invert(x) {
    return napi.vestaInvert(x);
}

export function eq(x) {
    return function(y) {
        return napi.vestaEq(x, y);
    };
}

export function toString(x) {
    return napi.vestaToString(x);
}

export function rand(seed) {
    return napi.vestaRand(seed);
}