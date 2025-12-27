import { createRequire } from 'module';
const require = createRequire(import.meta.url);
const crypto = require('snarky-crypto');

export const verifyPallasPoseidonGadget = crypto.verifyPallasPoseidonGadget;
export const verifyVestaPoseidonGadget = crypto.verifyVestaPoseidonGadget;