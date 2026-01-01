import { createRequire } from 'module';
const require = createRequire(import.meta.url);
const crypto = require('snarky-crypto');

export const verifyPallasGeneric = (coeffs) => (witness) => {
  return crypto.verifyPallasGeneric(coeffs, witness);
};

export const verifyVestaGeneric = (coeffs) => (witness) => {
  return crypto.verifyVestaGeneric(coeffs, witness);
};