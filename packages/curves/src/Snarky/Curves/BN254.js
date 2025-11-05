import { createRequire } from 'module';
const require = createRequire(import.meta.url);
const napi = require('curves-napi');

export function zero() {
    return napi.bn254Zero();
}

export function one() {
    return napi.bn254One();
}

export function mul(x) {
    return function(y) {
        return napi.bn254Mul(x, y);
    };
}

export function add(x) {
    return function(y) {
        return napi.bn254Add(x, y);
    };
}

export function sub(x) {
    return function(y) {
        return napi.bn254Sub(x, y);
    };
}

export function div(x) {
    return function(y) {
        return napi.bn254Div(x, y);
    };
}

export function invert(x) {
    return napi.bn254Invert(x);
}

export function eq(x) {
    return function(y) {
        return napi.bn254Eq(x, y);
    };
}

export function toString(x) {
    return napi.bn254ToString(x);
}

export function rand(seed) {
    return napi.bn254Rand(seed);
}