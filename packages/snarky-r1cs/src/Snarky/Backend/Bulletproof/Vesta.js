import { createRequire } from 'module';
const require = createRequire(import.meta.url);
const crypto = require('snarky-crypto');

// CRS functions
export const vestaCrsCreate = crypto.vestaCrsCreate;
export const vestaCrsSize = crypto.vestaCrsSize;

// Witness functions  
export const vestaWitnessCreate = crypto.vestaWitnessCreate;
export const vestaWitnessSize = crypto.vestaWitnessSize;

// Statement functions
export const vestaStatementCreate = crypto.vestaStatementCreate;

// Circuit functions
export const vestaCircuitCreate = crypto.vestaCircuitCreate;
export const vestaCircuitN = crypto.vestaCircuitN;
export const vestaCircuitQ = crypto.vestaCircuitQ;
export const vestaCircuitIsSatisfiedBy = crypto.vestaCircuitIsSatisfiedBy;

// Proving and verification
export const vestaProve = crypto.vestaProve;
export const vestaVerify = crypto.vestaVerify;