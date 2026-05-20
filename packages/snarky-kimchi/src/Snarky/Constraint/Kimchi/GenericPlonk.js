import { createRequire } from 'module';
const require = createRequire(import.meta.url);
const crypto = require('snarky-crypto');

// FIELD-REP COMPAT SHIM — coeffs/witness are now bigint[]; convert at
// the snarky-crypto boundary. Pallas scalar = Fq, Vesta scalar = Fp.
const toFq = (b) => crypto.pallasScalarfieldFromBigint(b);
const toFp = (b) => crypto.vestaScalarfieldFromBigint(b);

export const verifyPallasGeneric = (coeffs) => (witness) =>
  crypto.verifyPallasGeneric(coeffs.map(toFq), witness.map(toFq));

export const verifyVestaGeneric = (coeffs) => (witness) =>
  crypto.verifyVestaGeneric(coeffs.map(toFp), witness.map(toFp));
