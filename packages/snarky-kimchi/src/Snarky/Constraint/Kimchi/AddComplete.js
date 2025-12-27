import { createRequire } from 'module';
const require = createRequire(import.meta.url);
const crypto = require('snarky-crypto');

export const verifyPallasCompleteAddGadget = crypto.verifyPallasCompleteAdd;
export const verifyVestaCompleteAddGadget = crypto.verifyVestaCompleteAdd;