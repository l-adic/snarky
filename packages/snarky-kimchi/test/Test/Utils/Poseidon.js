import { createRequire } from 'module';
const require = createRequire(import.meta.url);
const crypto = require('snarky-crypto');

export const makePallasPoseidonVerifier = crypto.makePallasPoseidonVerifier;

export const verifyPallasPoseidonGadget = crypto.verifyPallasPoseidonGadget;

export const makeVestaPoseidonVerifier = crypto.makeVestaPoseidonVerifier;

export const verifyVestaPoseidonGadget = crypto.verifyVestaPoseidonGadget;