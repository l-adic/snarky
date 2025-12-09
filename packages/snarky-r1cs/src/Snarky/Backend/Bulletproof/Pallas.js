import { createRequire } from 'module';
const require = createRequire(import.meta.url);
const crypto = require('snarky-crypto');

// CRS functions
export const pallasCrsCreate = crypto.pallasCrsCreate;
export const pallasCrsSize = crypto.pallasCrsSize;

// Witness functions  
export const pallasWitnessCreate = crypto.pallasWitnessCreate;
export const pallasWitnessSize = crypto.pallasWitnessSize;

// Statement functions
export const pallasStatementCreate = crypto.pallasStatementCreate;

// Circuit functions
export const pallasCircuitCreate = crypto.pallasCircuitCreate;
export const pallasCircuitN = crypto.pallasCircuitN;
export const pallasCircuitQ = crypto.pallasCircuitQ;
export const pallasCircuitIsSatisfiedBy = crypto.pallasCircuitIsSatisfiedBy;

// Proving and verification
export const pallasProve = crypto.pallasProve;
export const pallasVerify = crypto.pallasVerify;