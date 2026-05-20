import { createRequire } from 'module';
const require = createRequire(import.meta.url);
const crypto = require('snarky-crypto');

// FIELD-REP COMPAT SHIM — `witness` is `Vector 2 (Vector 15 F)`
// = `Array<Array<bigint>>` now; convert to Externals.
const toFq = (b) => crypto.pallasScalarfieldFromBigint(b);
const toFp = (b) => crypto.vestaScalarfieldFromBigint(b);

export const verifyPallasVarBaseMulGadget = (witness) =>
  crypto.verifyPallasVarbasemul(witness.map((row) => row.map(toFq)));

export const verifyVestaVarBaseMulGadget = (witness) =>
  crypto.verifyVestaVarbasemul(witness.map((row) => row.map(toFp)));
