import { createRequire } from 'module';
const require = createRequire(import.meta.url);
const crypto = require('snarky-crypto');

// Setup functions - using new separated API
export const bn254Setup = function(dimensions, matrixA, matrixB, matrixC, seed) {
  // Create circuit (constraints only)
  const circuit = crypto.bn254CircuitCreate(dimensions, matrixA, matrixB, matrixC);
  
  // Setup from circuit
  const result = crypto.bn254Setup(circuit, seed);
  
  // Convert array to PureScript Tuple format
  return { value0: result[0], value1: result[1] };
};

// Proving and verification - using new separated API
export const bn254Prove = function(pk, dimensions, matrixA, matrixB, matrixC, witness, publicInputs, seed) {
  // Create circuit (constraints only)
  const circuit = crypto.bn254CircuitCreate(dimensions, matrixA, matrixB, matrixC);
  
  // Create witness separately
  const witnessObj = crypto.bn254WitnessCreate(witness, publicInputs);
  
  // Prove using separated objects
  return crypto.bn254Prove(pk, circuit, witnessObj, seed);
};

export const bn254Verify = function(vk, proof, publicInputs) {
  return crypto.bn254Verify(vk, proof, publicInputs);
};

// Circuit satisfaction checking - using new separated API
export const bn254CircuitCheckSatisfaction = function(dimensions, matrixA, matrixB, matrixC, witness, publicInputs) {
  // Create circuit (constraints only)
  const circuit = crypto.bn254CircuitCreate(dimensions, matrixA, matrixB, matrixC);
  
  // Create witness separately
  const witnessObj = crypto.bn254WitnessCreate(witness, publicInputs);
  
  // Check satisfaction using separated objects
  return crypto.bn254CircuitIsSatisfiedBy(circuit, witnessObj);
};