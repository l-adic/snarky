import { createRequire } from 'module';
const require = createRequire(import.meta.url);
const crypto = require('snarky-crypto');

// Setup functions
export const bn254Setup = function(dimensions, matrixA, matrixB, matrixC, seed) {
  const result = crypto.bn254Setup(dimensions, matrixA, matrixB, matrixC, seed);
  // Convert array to PureScript Tuple format
  return { value0: result[0], value1: result[1] };
};

// Proving and verification  
export const bn254Prove = function(pk, dimensions, matrixA, matrixB, matrixC, witness, publicInputs, seed) {
  return crypto.bn254Prove(pk, dimensions, matrixA, matrixB, matrixC, witness, publicInputs, seed);
};

export const bn254Verify = function(vk, proof, publicInputs) {
  return crypto.bn254Verify(vk, proof, publicInputs);
};

// Circuit satisfaction checking
export const bn254CircuitCheckSatisfaction = function(dimensions, matrixA, matrixB, matrixC, witness, publicInputs) {
  return crypto.bn254CircuitCheckSatisfaction(dimensions, matrixA, matrixB, matrixC, witness, publicInputs);
};