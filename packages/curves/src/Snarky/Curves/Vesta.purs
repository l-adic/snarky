-- | Convenience module for the Vesta curve.
-- |
-- | Re-exports Vesta types with shorter names for use in circuit code.
-- |
-- | ```purescript
-- | import Snarky.Curves.Vesta as Vesta
-- |
-- | myScalar :: Vesta.ScalarField
-- | myPoint :: Vesta.G
-- | ```
module Snarky.Curves.Vesta
  ( ScalarField
  , BaseField
  , G
  ) where

import Snarky.Curves.Pasta (VestaBaseField, VestaG, VestaScalarField)

-- | Vesta scalar field (F_r). Use for scalar multiplication.
type ScalarField = VestaScalarField

-- | Vesta base field (F_q). Equal to `Pallas.ScalarField`.
type BaseField = VestaBaseField

-- | Vesta curve group. Points on y² = x³ + 5 over BaseField.
type G = VestaG

