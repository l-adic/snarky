-- | Public interface for linearization polynomials.
-- |
-- | This module provides type-safe linearization polynomials for PLONK verification.
-- | The linearizations are curve-specific and parameterized by the circuit field.
-- |
-- | Usage:
-- | - For circuits on Fp (Vesta.ScalarField) verifying Pallas-based proofs: use `pallas`
-- | - For circuits on Fq (Pallas.ScalarField) verifying Vesta-based proofs: use `vesta`
module Pickles.Linearization
  ( module ReExports
  , pallas
  , vesta
  ) where

import Pickles.Linearization.Pallas as Pallas
import Pickles.Linearization.Types (LinearizationPoly) as ReExports
import Pickles.Linearization.Types (LinearizationPoly, mkLinearizationPoly)
import Pickles.Linearization.Vesta as Vesta
import Snarky.Curves.Pallas as PallasCurve
import Snarky.Curves.Vesta as VestaCurve

-- | Linearization for Pallas constraint systems.
-- | Use when verifying proofs from circuits with Pallas commitments.
-- | These proofs are verified by circuits running on Vesta.ScalarField (Fp).
pallas :: LinearizationPoly VestaCurve.ScalarField
pallas = mkLinearizationPoly Pallas.constantTermTokens

-- | Linearization for Vesta constraint systems.
-- | Use when verifying proofs from circuits with Vesta commitments.
-- | These proofs are verified by circuits running on Pallas.ScalarField (Fq).
vesta :: LinearizationPoly PallasCurve.ScalarField
vesta = mkLinearizationPoly Vesta.constantTermTokens
