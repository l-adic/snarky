-- | The two Pasta-cycle protocol fields. Both step and wrap circuits
-- | reason about both, so the types live at tier 0 rather than inside
-- | either side's namespace.
-- |
-- |   `StepField` — Fp = Vesta.ScalarField = Pallas.BaseField
-- |                 (the step circuit's native field)
-- |   `WrapField` — Fq = Pallas.ScalarField = Vesta.BaseField
-- |                 (the wrap circuit's native field)
module Pickles.Field
  ( StepField
  , WrapField
  ) where

import Snarky.Curves.Pallas as Pallas
import Snarky.Curves.Vesta as Vesta

-- | Step circuit f (Fp = Vesta.ScalarField = Pallas.BaseField).
type StepField = Vesta.ScalarField

-- | Wrap circuit f (Fq = Pallas.ScalarField = Vesta.BaseField).
type WrapField = Pallas.ScalarField
