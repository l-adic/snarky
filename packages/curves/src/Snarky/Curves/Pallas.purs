-- | Convenience module for the Pallas curve.
-- |
-- | Re-exports Pallas types with shorter names for use in circuit code.
-- |
-- | ```purescript
-- | import Snarky.Curves.Pallas as Pallas
-- |
-- | myScalar :: Pallas.ScalarField
-- | myPoint :: Pallas.G
-- | ```
module Snarky.Curves.Pallas
  ( ScalarField
  , BaseField
  , G
  ) where

import Snarky.Curves.Pasta (PallasBaseField, PallasG, PallasScalarField)

-- | Pallas scalar field (F_r). Use for scalar multiplication.
type ScalarField = PallasScalarField

-- | Pallas base field (F_q). Equal to `Vesta.ScalarField`.
type BaseField = PallasBaseField

-- | Pallas curve group. Points on y² = x³ + 5 over BaseField.
type G = PallasG

