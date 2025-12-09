import { createRequire } from 'module';
const require = createRequire(import.meta.url);
const napi = require('snarky-crypto');

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

export function _toAffine(just, nothing, value) {
  let p = napi.vestaGroupToAffine(value)
  if (p == null) {
    return nothing;
  } else {
    return just([p[0], p[1]]);
  }
}