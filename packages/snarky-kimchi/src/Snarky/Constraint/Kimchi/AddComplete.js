import { createRequire } from 'module';
const require = createRequire(import.meta.url);
const crypto = require('snarky-crypto');

// FIELD-REP COMPAT SHIM — `witness_row` is `Vector 15 BaseField`
// = `Array<bigint>` now. Pallas.BaseField = Fp (= VestaScalarField in
// snarky-crypto naming); Vesta.BaseField = Fq (= PallasScalarField).
const toFp = (b) => crypto.vestaScalarfieldFromBigint(b);
const toFq = (b) => crypto.pallasScalarfieldFromBigint(b);

export const verifyPallasCompleteAddGadget = (witness) =>
  crypto.verifyPallasCompleteAdd(witness.map(toFp));

export const verifyVestaCompleteAddGadget = (witness) =>
  crypto.verifyVestaCompleteAdd(witness.map(toFq));
