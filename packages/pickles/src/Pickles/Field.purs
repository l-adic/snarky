-- | The two Pasta-cycle protocol fields. Both circuits reason about
-- | both fields, so neither type belongs in a step- or wrap-specific
-- | namespace.
module Pickles.Field
  ( StepField
  , WrapField
  ) where

import Snarky.Curves.Pallas as Pallas
import Snarky.Curves.Vesta as Vesta

-- | The step circuit's native field: Fp = Vesta.ScalarField =
-- | Pallas.BaseField.
type StepField = Vesta.ScalarField

-- | The wrap circuit's native field: Fq = Pallas.ScalarField =
-- | Vesta.BaseField.
type WrapField = Pallas.ScalarField
