import { createRequire } from 'module';
const require = createRequire(import.meta.url);
const crypto = require('snarky-crypto');

// Circuit creation (following bulletproofs pattern)
export const bn254CircuitCreate = function(dimensions, matrixA, matrixB, matrixC, publicInputIndices) {
  return crypto.bn254CircuitCreate(dimensions, matrixA, matrixB, matrixC, publicInputIndices);
};

// Witness creation
export const bn254WitnessCreate = function(witness) {
  return crypto.bn254WitnessCreate(witness);
};

// Setup from circuit
export const bn254Setup = function(circuit, seed) {
  const result = crypto.bn254Setup(circuit, seed);
  // Convert array to PureScript Tuple format
  return { value0: result[0], value1: result[1] };
};

// Circuit satisfaction check
export const bn254CircuitIsSatisfiedBy = function(circuit, witness) {
  return crypto.bn254CircuitIsSatisfiedBy(circuit, witness);
};

// Prove using circuit and witness
export const bn254Prove = function(pk, circuit, witness, seed) {
  return crypto.bn254Prove(pk, circuit, witness, seed);
};

// Verify
export const bn254Verify = crypto.bn254Verify;