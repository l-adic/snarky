import { createRequire } from 'module';
const require = createRequire(import.meta.url);
const napi = require('snarky-crypto');

// FIELD-REP COMPAT SHIM — `initWithDomain` returns `Vector 3 BaseField`.
// Pallas.BaseField = Fp (= VestaScalarField); Vesta.BaseField = Fq
// (= PallasScalarField). Convert each External to bigint.
const fromFp = (e) => napi.vestaScalarfieldToBigint(e);
const fromFq = (e) => napi.pallasScalarfieldToBigint(e);

export function pallasInitWithDomain(domain) {
    return napi.pallasInitWithDomain(domain).map(fromFp);
}

export function vestaInitWithDomain(domain) {
    return napi.vestaInitWithDomain(domain).map(fromFq);
}
