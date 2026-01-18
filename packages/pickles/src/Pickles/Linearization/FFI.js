import { createRequire } from 'module';
const require = createRequire(import.meta.url);
const crypto = require('snarky-crypto');

// Effect-returning versions (for compatibility)
export const evaluatePallasLinearizationImpl =
  (alpha) => (beta) => (gamma) => (jointCombiner) =>
  (witnessEvals) => (coefficientEvals) =>
  (poseidonIndex) => (genericIndex) => (varbasemulIndex) =>
  (endomulIndex) => (endomulScalarIndex) => (completeAddIndex) =>
  (vanishesOnZk) => (zeta) => (domainLog2) => () => {
    return crypto.evaluatePallasLinearization(
      alpha, beta, gamma, jointCombiner,
      witnessEvals, coefficientEvals,
      poseidonIndex, genericIndex, varbasemulIndex,
      endomulIndex, endomulScalarIndex, completeAddIndex,
      vanishesOnZk, zeta, domainLog2
    );
  };

export const evaluateVestaLinearizationImpl =
  (alpha) => (beta) => (gamma) => (jointCombiner) =>
  (witnessEvals) => (coefficientEvals) =>
  (poseidonIndex) => (genericIndex) => (varbasemulIndex) =>
  (endomulIndex) => (endomulScalarIndex) => (completeAddIndex) =>
  (vanishesOnZk) => (zeta) => (domainLog2) => () => {
    return crypto.evaluateVestaLinearization(
      alpha, beta, gamma, jointCombiner,
      witnessEvals, coefficientEvals,
      poseidonIndex, genericIndex, varbasemulIndex,
      endomulIndex, endomulScalarIndex, completeAddIndex,
      vanishesOnZk, zeta, domainLog2
    );
  };

// Pure versions (for use in QuickCheck and other pure contexts)
export const evaluatePallasLinearizationPureImpl = (input) =>
  crypto.evaluatePallasLinearization(
    input.alpha, input.beta, input.gamma, input.jointCombiner,
    input.witnessEvals, input.coefficientEvals,
    input.poseidonIndex, input.genericIndex, input.varbasemulIndex,
    input.endomulIndex, input.endomulScalarIndex, input.completeAddIndex,
    input.vanishesOnZk, input.zeta, input.domainLog2
  );

export const evaluateVestaLinearizationPureImpl = (input) =>
  crypto.evaluateVestaLinearization(
    input.alpha, input.beta, input.gamma, input.jointCombiner,
    input.witnessEvals, input.coefficientEvals,
    input.poseidonIndex, input.genericIndex, input.varbasemulIndex,
    input.endomulIndex, input.endomulScalarIndex, input.completeAddIndex,
    input.vanishesOnZk, input.zeta, input.domainLog2
  );

// ============================================================================
// Domain polynomial functions for linearization
// ============================================================================

// Unnormalized Lagrange basis: (pt^n - 1) / (pt - ω^i)
// zkRows: Boolean indicating whether to offset into ZK region
// offset: i32 row offset

export const pallasUnnormalizedLagrangeBasisImpl = ({ domainLog2, zkRows, offset, pt }) =>
  crypto.pallasUnnormalizedLagrangeBasis(domainLog2, zkRows, offset, pt);

export const vestaUnnormalizedLagrangeBasisImpl = ({ domainLog2, zkRows, offset, pt }) =>
  crypto.vestaUnnormalizedLagrangeBasis(domainLog2, zkRows, offset, pt);

// VanishesOnZkAndPreviousRows: ∏_{j=0}^{zkRows} (pt - ω^(n - zkRows - 1 + j))
// zkRows: number of zero-knowledge rows (typically 3)

export const pallasVanishesOnZkAndPreviousRowsImpl = ({ domainLog2, zkRows, pt }) =>
  crypto.pallasVanishesOnZkAndPreviousRows(domainLog2, zkRows, pt);

export const vestaVanishesOnZkAndPreviousRowsImpl = ({ domainLog2, zkRows, pt }) =>
  crypto.vestaVanishesOnZkAndPreviousRows(domainLog2, zkRows, pt);
