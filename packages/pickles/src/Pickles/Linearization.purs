-- | The two deployed linearization polynomials, one per curve. Each is
-- | named for the curve whose proofs it verifies, not for the field the
-- | verifying circuit runs on.
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

-- | Linearization for proofs carrying Pallas commitments, verified by
-- | a circuit over Fp.
pallas :: LinearizationPoly VestaCurve.ScalarField
pallas = mkLinearizationPoly Pallas.constantTermTokens

-- | Linearization for proofs carrying Vesta commitments, verified by
-- | a circuit over Fq.
vesta :: LinearizationPoly PallasCurve.ScalarField
vesta = mkLinearizationPoly Vesta.constantTermTokens
