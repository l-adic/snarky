import { createRequire } from 'module';
const require = createRequire(import.meta.url);
const crypto = require('snarky-crypto');

// Linearization evaluation - accepts a record, spreads to curried Rust FFI
export const evaluatePallasLinearizationImpl = (input) =>
  crypto.evaluatePallasLinearization(
    input.alpha, input.beta, input.gamma, input.jointCombiner,
    input.witnessEvals, input.coefficientEvals,
    input.poseidonIndex, input.genericIndex, input.varbasemulIndex,
    input.endomulIndex, input.endomulScalarIndex, input.completeAddIndex,
    input.vanishesOnZk, input.zeta, input.domainLog2
  );

export const evaluateVestaLinearizationImpl = (input) =>
  crypto.evaluateVestaLinearization(
    input.alpha, input.beta, input.gamma, input.jointCombiner,
    input.witnessEvals, input.coefficientEvals,
    input.poseidonIndex, input.genericIndex, input.varbasemulIndex,
    input.endomulIndex, input.endomulScalarIndex, input.completeAddIndex,
    input.vanishesOnZk, input.zeta, input.domainLog2
  );

// Domain polynomial functions
export const pallasUnnormalizedLagrangeBasisImpl = ({ domainLog2, zkRows, offset, pt }) =>
  crypto.pallasUnnormalizedLagrangeBasis(domainLog2, zkRows, offset, pt);

export const vestaUnnormalizedLagrangeBasisImpl = ({ domainLog2, zkRows, offset, pt }) =>
  crypto.vestaUnnormalizedLagrangeBasis(domainLog2, zkRows, offset, pt);

export const pallasVanishesOnZkAndPreviousRowsImpl = ({ domainLog2, zkRows, pt }) =>
  crypto.pallasVanishesOnZkAndPreviousRows(domainLog2, zkRows, pt);

export const vestaVanishesOnZkAndPreviousRowsImpl = ({ domainLog2, zkRows, pt }) =>
  crypto.vestaVanishesOnZkAndPreviousRows(domainLog2, zkRows, pt);

// Witness to polynomial evaluations
export const pallasWitnessToEvaluationsImpl = (witness) => (zeta) => (domainLog2) =>
  crypto.pallasWitnessToEvaluations(witness, zeta, domainLog2);

export const vestaWitnessToEvaluationsImpl = (witness) => (zeta) => (domainLog2) =>
  crypto.vestaWitnessToEvaluations(witness, zeta, domainLog2);

// Gates to coefficient polynomial evaluations
// Note: For Pallas linearization, we use Vesta gates (they share field Fp)
export const pallasGatesToCoefficientEvaluationsImpl = (gates) => (zeta) => (domainLog2) =>
  crypto.pallasGatesToCoefficientEvaluations(gates, zeta, domainLog2);

export const vestaGatesToCoefficientEvaluationsImpl = (gates) => (zeta) => (domainLog2) =>
  crypto.vestaGatesToCoefficientEvaluations(gates, zeta, domainLog2);

// Gates to selector polynomial evaluations
export const pallasGatesToSelectorEvaluationsImpl = (gates) => (zeta) => (domainLog2) =>
  crypto.pallasGatesToSelectorEvaluations(gates, zeta, domainLog2);

export const vestaGatesToSelectorEvaluationsImpl = (gates) => (zeta) => (domainLog2) =>
  crypto.vestaGatesToSelectorEvaluations(gates, zeta, domainLog2);

// Prover index to polynomial evaluations (for linearization testing with valid witnesses)
// For Pallas linearization (verifies Vesta circuits, uses Vesta prover index)
export const pallasProverIndexWitnessEvaluationsImpl = (proverIndex) => (witnessColumns) => (zeta) =>
  crypto.pallasProverIndexWitnessEvaluations(proverIndex, witnessColumns, zeta);

export const pallasProverIndexCoefficientEvaluationsImpl = (proverIndex) => (zeta) =>
  crypto.pallasProverIndexCoefficientEvaluations(proverIndex, zeta);

export const pallasProverIndexSelectorEvaluationsImpl = (proverIndex) => (zeta) =>
  crypto.pallasProverIndexSelectorEvaluations(proverIndex, zeta);

// For Vesta linearization (verifies Pallas circuits, uses Pallas prover index)
export const vestaProverIndexWitnessEvaluationsImpl = (proverIndex) => (witnessColumns) => (zeta) =>
  crypto.vestaProverIndexWitnessEvaluations(proverIndex, witnessColumns, zeta);

export const vestaProverIndexCoefficientEvaluationsImpl = (proverIndex) => (zeta) =>
  crypto.vestaProverIndexCoefficientEvaluations(proverIndex, zeta);

export const vestaProverIndexSelectorEvaluationsImpl = (proverIndex) => (zeta) =>
  crypto.vestaProverIndexSelectorEvaluations(proverIndex, zeta);
