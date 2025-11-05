import { createRequire } from 'module';
const require = createRequire(import.meta.url);
const napi = require('./pallas-napi.node');

export function zero() {
    return napi.zero();
}

export function one() {
    return napi.one();
}

export function mul(x) {
    return function(y) {
        return napi.mul(x, y);
    };
}

export function add(x) {
    return function(y) {
        return napi.add(x, y);
    };
}

export function sub(x) {
    return function(y) {
        return napi.sub(x, y);
    };
}

export function div(x) {
    return function(y) {
        return napi.div(x, y);
    };
}

export function invert(x) {
    return napi.invert(x);
}

export function eq(x) {
    return function(y) {
        return napi.eq(x, y);
    };
}

export function toString(x) {
    return napi.toString(x);
}