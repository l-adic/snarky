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
