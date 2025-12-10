import { createRequire } from 'module';
const require = createRequire(import.meta.url);
const crypto = require('snarky-crypto');

// CRS functions
export const vestaCrsCreate = crypto.vestaCrsCreate;

// Witness functions  
export const vestaWitnessCreate = crypto.vestaWitnessCreate;

// Statement functions
export const vestaStatementCreate = crypto.vestaStatementCreate;

// Circuit functions
export const vestaCircuitCreate = crypto.vestaCircuitCreate;
export const vestaCircuitIsSatisfiedBy = crypto.vestaCircuitIsSatisfiedBy;

// Proving and verification
export const vestaProve = crypto.vestaProve;
export const vestaVerify = crypto.vestaVerify;