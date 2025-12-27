import { createRequire } from 'module';
const require = createRequire(import.meta.url);
const crypto = require('snarky-crypto');

export const verifyPallasVarBaseMulGadget = crypto.verifyPallasVarbasemul;
export const verifyVestaVarBaseMulGadget = crypto.verifyVestaVarbasemul;