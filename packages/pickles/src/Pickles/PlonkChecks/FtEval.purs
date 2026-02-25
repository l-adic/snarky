-- | Compute ft polynomial evaluation at zeta (ft_eval0).
-- |
-- | This module composes the permutation contribution and gate constraints
-- | to compute ft_eval0, which is used in the combined inner product check.
-- |
-- | The formula is:
-- |   ft_eval0 = permContribution + publicEval - gateConstraints
-- |
-- | Where:
-- | - permContribution: Permutation argument contribution (from Permutation.purs)
-- | - publicEval: Public input polynomial evaluation at zeta (witness input)
-- | - gateConstraints: Gate constraint polynomial (linearization constant term)
-- |
-- | Reference: mina/src/lib/pickles/plonk_checks/plonk_checks.ml (ft_eval0)
module Pickles.PlonkChecks.FtEval
  ( ftEval0
  , ftEval0Circuit
  , ftEval0CircuitM
  ) where

import Prelude

import Pickles.Linearization.FFI (class LinearizationFFI)
import Pickles.Linearization.Types (LinearizationPoly)
import Pickles.PlonkChecks.GateConstraints (GateConstraintInput, evaluateGateConstraints, evaluateGateConstraintsM)
import Pickles.PlonkChecks.Permutation (PermutationInput, permContributionCircuit)
import Poseidon (class PoseidonField)
import Snarky.Circuit.DSL (class CircuitM, FVar, Snarky, add_, sub_)
import Snarky.Curves.Class (class HasEndo, class PrimeField)

-------------------------------------------------------------------------------
-- | Pure (Field-level) computation
-------------------------------------------------------------------------------

-- | Compute ft_eval0 at the field level.
-- |
-- | ft_eval0 = permContribution + publicEval - gateConstraints
-- |
-- | This is used by the combined inner product check to verify the
-- | polynomial opening.
-- |
-- | Note: For gate constraints, this function takes the pre-evaluated
-- | constant term (from `Pickles.Linearization.Interpreter.evaluate`).
-- | See `Test.Pickles.E2E.permutationTest` for example usage.
ftEval0
  :: forall f
   . Ring f
  => { permContribution :: f
     , publicEval :: f
     , gateConstraints :: f
     }
  -> f
ftEval0 { permContribution: perm, publicEval, gateConstraints } =
  perm + publicEval - gateConstraints

-------------------------------------------------------------------------------
-- | Circuit-level computation
-------------------------------------------------------------------------------

-- | Compute ft_eval0 in-circuit.
-- |
-- | ft_eval0 = permContribution + publicEval - gateConstraints
-- |
-- | The `publicEval` is provided as a witness input. The prover supplies
-- | the correct value, and the opening proof verifies all polynomial
-- | evaluations are correct.
-- |
-- | This function computes:
-- | - permContribution via `permContributionCircuit`
-- | - gateConstraints via `evaluateGateConstraints`
-- | - Combines them with the provided publicEval witness
ftEval0Circuit
  :: forall f f' c t m
   . PrimeField f
  => PoseidonField f
  => HasEndo f f'
  => CircuitM f c t m
  => LinearizationPoly f
  -> { permInput :: PermutationInput (FVar f)
     , gateInput :: GateConstraintInput (FVar f)
     , publicEval :: FVar f
     }
  -> Snarky c t m (FVar f)
ftEval0Circuit linPoly { permInput, gateInput, publicEval } = do
  -- Compute permutation contribution in-circuit
  perm <- permContributionCircuit permInput

  -- Compute gate constraints in-circuit
  gate <- evaluateGateConstraints linPoly gateInput

  -- ft_eval0 = perm + publicEval - gate
  let permPlusPublic = add_ perm publicEval
  pure $ sub_ permPlusPublic gate

-- | Monadic version of ftEval0Circuit using precomputed alpha powers.
-- | Uses evaluateGateConstraintsM which matches OCaml's scalars_env approach.
ftEval0CircuitM
  :: forall f f' g c t m
   . PrimeField f
  => PoseidonField f
  => HasEndo f f'
  => CircuitM f c t m
  => LinearizationFFI f g
  => LinearizationPoly f
  -> Int -- ^ domainLog2
  -> FVar f -- ^ zeta (expanded)
  -> { permInput :: PermutationInput (FVar f)
     , gateInput :: GateConstraintInput (FVar f)
     , publicEval :: FVar f
     }
  -> Snarky c t m (FVar f)
ftEval0CircuitM linPoly domLog2 zeta { permInput, gateInput, publicEval } = do
  perm <- permContributionCircuit permInput
  gate <- evaluateGateConstraintsM linPoly domLog2 zeta gateInput
  let permPlusPublic = add_ perm publicEval
  pure $ sub_ permPlusPublic gate
