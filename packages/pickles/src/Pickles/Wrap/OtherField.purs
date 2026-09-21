-- | How the wrap circuit carries values of the other field.
-- |
-- | The wrap circuit's native field is `WrapField` (Fq); the step
-- | proof's scalars live in `StepField` (Fp), which is smaller, so each
-- | one fits in a single wrap-field element. The step-side counterpart
-- | is `Pickles.Step.OtherField`, where the inclusion runs the other
-- | way.
module Pickles.Wrap.OtherField
  ( WrapOtherField
  , ipaScalarOps
  , fopShiftOps
  ) where

import Prelude

import Pickles.ShiftOps (IpaScalarOps)
import Snarky.Circuit.DSL (BoolVar, FVar, Snarky, label, seal)
import Snarky.Circuit.Kimchi (Type1(..), Type2(..), fromShiftedType1Circuit, fromShiftedType2Circuit, scaleFast1, shiftedEqualType1, shiftedEqualType2)
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Curves.Class (class FieldSizeInBits, class PrimeField)

-- | A step-field value held in one wrap-field variable, under the
-- | Type1 shift `s = 2*t + 2^n + 1`.
type WrapOtherField f = Type1 f

-- | The IPA scalar operations for the wrap circuit. `z1`, `z2`, the
-- | combined inner product and `b` are all step-field values, so they
-- | use the single-element Type1 representation.
ipaScalarOps
  :: forall f r
   . FieldSizeInBits f 255
  => PrimeField f
  => IpaScalarOps f r (WrapOtherField (FVar f))
ipaScalarOps =
  { scaleByShifted: \p t -> scaleFast1 @51 p t
  , scaleByCip: \p t -> scaleFast1 @51 p t
  , shiftedToAbsorbFields: \(Type1 t) -> [ t ]
  , unshift: fromShiftedType1Circuit
  , shiftedEqual: shiftedEqualType1
  }

-- | The shift operations `wrapFinalizeOtherProofCircuit` uses. Deferred
-- | values arrive under the Type2 shift `x + 2^n`, not the Type1 shift
-- | the IPA scalars use.
fopShiftOps
  :: forall @f r
   . FieldSizeInBits f 255
  => PrimeField f
  => { unshift :: Type2 (FVar f) -> FVar f
     , shiftedEqual :: Type2 (FVar f) -> FVar f -> Snarky f (KimchiConstraint f) r (BoolVar f)
     , sealInner :: Type2 (FVar f) -> Snarky f (KimchiConstraint f) r (Type2 (FVar f))
     }
fopShiftOps =
  { unshift: fromShiftedType2Circuit
  , shiftedEqual: shiftedEqualType2
  , sealInner: \(Type2 x) -> Type2 <$> label "seal_shifted_inner" (seal x)
  }
