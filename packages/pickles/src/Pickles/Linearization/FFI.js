import { createRequire } from 'module';
const require = createRequire(import.meta.url);
const crypto = require('snarky-crypto');

// Helper: restructure flat paired array into [{zeta, omegaTimesZeta}, ...]
const pairEvals = (flat) => {
  const result = [];
  for (let i = 0; i < flat.length; i += 2) {
    result.push({ zeta: flat[i], omegaTimesZeta: flat[i + 1] });
  }
  return result;
};

// Helper: flatten a PointEval record to [zeta, omegaTimesZeta]
const flattenPointEval = (pe) => [pe.zeta, pe.omegaTimesZeta];

// Linearization evaluation
export const evaluatePallasLinearization = (input) =>
  crypto.evaluatePallasLinearization(
    input.alpha, input.beta, input.gamma, input.jointCombiner,
    input.witnessEvals.flatMap(flattenPointEval), input.coefficientEvals,
    flattenPointEval(input.poseidonIndex), flattenPointEval(input.genericIndex),
    flattenPointEval(input.varbasemulIndex), flattenPointEval(input.endomulIndex),
    flattenPointEval(input.endomulScalarIndex), flattenPointEval(input.completeAddIndex),
    input.vanishesOnZk, input.zeta, input.domainLog2
  );

export const evaluateVestaLinearization = (input) =>
  crypto.evaluateVestaLinearization(
    input.alpha, input.beta, input.gamma, input.jointCombiner,
    input.witnessEvals.flatMap(flattenPointEval), input.coefficientEvals,
    flattenPointEval(input.poseidonIndex), flattenPointEval(input.genericIndex),
    flattenPointEval(input.varbasemulIndex), flattenPointEval(input.endomulIndex),
    flattenPointEval(input.endomulScalarIndex), flattenPointEval(input.completeAddIndex),
    input.vanishesOnZk, input.zeta, input.domainLog2
  );

// Domain polynomial functions
export const pallasUnnormalizedLagrangeBasis = ({ domainLog2, zkRows, offset, pt }) =>
  crypto.pallasUnnormalizedLagrangeBasis(domainLog2, zkRows, offset, pt);

export const vestaUnnormalizedLagrangeBasis = ({ domainLog2, zkRows, offset, pt }) =>
  crypto.vestaUnnormalizedLagrangeBasis(domainLog2, zkRows, offset, pt);

export const pallasVanishesOnZkAndPreviousRows = ({ domainLog2, zkRows, pt }) =>
  crypto.pallasVanishesOnZkAndPreviousRows(domainLog2, zkRows, pt);

export const vestaVanishesOnZkAndPreviousRows = ({ domainLog2, zkRows, pt }) =>
  crypto.vestaVanishesOnZkAndPreviousRows(domainLog2, zkRows, pt);

// Prover index domain
export const pallasProverIndexDomainLog2 = (proverIndex) =>
  crypto.pallasProverIndexDomainLog2(proverIndex);

export const vestaProverIndexDomainLog2 = (proverIndex) =>
  crypto.vestaProverIndexDomainLog2(proverIndex);

// Prover index polynomial evaluations
export const pallasProverIndexWitnessEvaluations = (proverIndex) => (witnessColumns) => (zeta) =>
  pairEvals(crypto.pallasProverIndexWitnessEvaluations(proverIndex, witnessColumns, zeta));

export const pallasProverIndexCoefficientEvaluations = (proverIndex) => (zeta) =>
  crypto.pallasProverIndexCoefficientEvaluations(proverIndex, zeta);

export const pallasProverIndexSelectorEvaluations = (proverIndex) => (zeta) =>
  pairEvals(crypto.pallasProverIndexSelectorEvaluations(proverIndex, zeta));

export const vestaProverIndexWitnessEvaluations = (proverIndex) => (witnessColumns) => (zeta) =>
  pairEvals(crypto.vestaProverIndexWitnessEvaluations(proverIndex, witnessColumns, zeta));

export const vestaProverIndexCoefficientEvaluations = (proverIndex) => (zeta) =>
  crypto.vestaProverIndexCoefficientEvaluations(proverIndex, zeta);

export const vestaProverIndexSelectorEvaluations = (proverIndex) => (zeta) =>
  pairEvals(crypto.vestaProverIndexSelectorEvaluations(proverIndex, zeta));

// Domain generators
export const pallasDomainGenerator = (domainLog2) =>
  crypto.pallasDomainGenerator(domainLog2);

export const vestaDomainGenerator = (domainLog2) =>
  crypto.vestaDomainGenerator(domainLog2);

// Domain shifts (7 permutation shifts, computed from domain_log2 alone)
export const pallasDomainShifts = (domainLog2) =>
  crypto.pallasDomainShifts(domainLog2);

export const vestaDomainShifts = (domainLog2) =>
  crypto.vestaDomainShifts(domainLog2);
