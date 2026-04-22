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
  ) where

import Prelude



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

