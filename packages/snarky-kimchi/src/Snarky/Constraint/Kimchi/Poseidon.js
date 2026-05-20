import { createRequire } from 'module';
const require = createRequire(import.meta.url);
const crypto = require('snarky-crypto');

// FIELD-REP COMPAT SHIM — `witness_matrix` is `Vector 12 (Vector 15 F)`
// = `Array<Array<bigint>>` now; convert deeply to snarky-crypto Externals.
const toFq = (b) => crypto.pallasScalarfieldFromBigint(b);
const toFp = (b) => crypto.vestaScalarfieldFromBigint(b);

export const verifyPallasPoseidonGadget = (numRows, witness) =>
  crypto.verifyPallasPoseidonGadget(numRows, witness.map((row) => row.map(toFq)));

export const verifyVestaPoseidonGadget = (numRows, witness) =>
  crypto.verifyVestaPoseidonGadget(numRows, witness.map((row) => row.map(toFp)));
