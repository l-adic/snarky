import { createRequire } from 'module';
const require = createRequire(import.meta.url);
const crypto = require('snarky-crypto');

export const bn254CircuitCreate = crypto.bn254CircuitCreate;
export const bn254WitnessCreate = crypto.bn254WitnessCreate;
export const bn254Setup = function(circuit, seed) {
  const result = crypto.bn254Setup(circuit, seed);
  return { value0: result[0], value1: result[1] };
};
export const bn254CircuitIsSatisfiedBy = crypto.bn254CircuitIsSatisfiedBy;
export const bn254Prove = crypto.bn254Prove;
export const bn254Verify = crypto.bn254Verify;