-- | The step circuit's representation of the other field.
-- |
-- | It works over Fp; the values it defers live in Fq, the larger of
-- | the two. Deferred values use `Type1`, a single shifted field
-- | element; IPA scalars use `Type2`'s `SplitField`, which covers all
-- | of Fq.
module Pickles.Step.OtherField
  ( StepOtherField
  , fopShiftOps
  , ipaScalarOps
  ) where

import Pickles.ShiftOps (FopShiftOps, IpaScalarOps)
import Safe.Coerce (coerce)
import Snarky.Circuit.DSL (Bool(..), BoolVar, FVar, equals_)
import Snarky.Circuit.Kimchi (SplitField(..), Type1, Type2(..), fromShiftedSplitFieldCircuit, fromShiftedType1Circuit, scaleFast2, shiftedEqualType1)
import Snarky.Curves.Class (class FieldSizeInBits, class PrimeField)

-- | An Fq deferred value in the step circuit: one shifted field
-- | element.
type StepOtherField f = Type1 f

-- | IPA scalar operations for the step circuit. `z1`, `z2`, the
-- | combined inner product and `b` are Fq values, so they take the
-- | `SplitField` representation.
ipaScalarOps
  :: forall f r
   . FieldSizeInBits f 255
  => PrimeField f
  => IpaScalarOps f r (Type2 (SplitField (FVar f) (BoolVar f)))
ipaScalarOps =
  { scaleByShifted: \p (Type2 (SplitField t)) -> scaleFast2 @51 @254 p t
  , shiftedToAbsorbFields: \(Type2 (SplitField { sDiv2, sOdd })) -> [ sDiv2, coerce sOdd ]
  , unshift: \(Type2 sf) -> fromShiftedSplitFieldCircuit sf
  , shiftedEqual: \(Type2 sf) raw -> equals_ (fromShiftedSplitFieldCircuit sf) raw
  }

-- | Unshift and shifted equality for the step circuit's
-- | `finalizeOtherProof`, at `Type1`.
fopShiftOps
  :: forall f r
   . FieldSizeInBits f 255
  => PrimeField f
  => FopShiftOps f r (StepOtherField (FVar f))
fopShiftOps =
  { unshift: fromShiftedType1Circuit
  , shiftedEqual: shiftedEqualType1
  }
