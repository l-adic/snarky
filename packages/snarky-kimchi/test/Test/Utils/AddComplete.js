import { createRequire } from 'module';
const require = createRequire(import.meta.url);
const crypto = require('snarky-crypto');

export const verifyPallasCompleteAdd = crypto.verifyPallasCompleteAdd;

export const verifyVestaCompleteAdd = crypto.verifyVestaCompleteAdd;