import { createRequire } from 'module';
const require = createRequire(import.meta.url);
const napi = require('snarky-crypto');

export function pallasInitWithDomain(domain) {
    return napi.pallasInitWithDomain(domain);
}

export function vestaInitWithDomain(domain) {
    return napi.vestaInitWithDomain(domain);
}
