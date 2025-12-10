import { createRequire } from 'module';
const require = createRequire(import.meta.url);
const crypto = require('snarky-crypto');

// CRS functions
export const pallasCrsCreate = crypto.pallasCrsCreate;

// Witness functions  
export const pallasWitnessCreate = crypto.pallasWitnessCreate;

// Statement functions
export const pallasStatementCreate = crypto.pallasStatementCreate;

// Circuit functions
export const pallasCircuitCreate = crypto.pallasCircuitCreate;
export const pallasCircuitIsSatisfiedBy = crypto.pallasCircuitIsSatisfiedBy;

// Proving and verification
export const pallasProve = crypto.pallasProve;
export const pallasVerify = crypto.pallasVerify;