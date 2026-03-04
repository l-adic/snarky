-- | Step circuit's cross-field representation.
-- |
-- | The Step circuit operates over Fp (Vesta.ScalarField). The "other field" is
-- | Fq (Pallas.ScalarField), which is LARGER than Fp.
-- |
-- | FOP deferred values use Type1 (single field element with shift 2*t + 2^n + 1).
-- | IPA scalars use Type2 (SplitField { sDiv2, sOdd }) for the full range of Fq.
-- |
-- | This module provides:
-- | - Type aliases for the Step circuit's FOP cross-field representation
-- | - IPA scalar ops (for checkBulletproof / ipaFinalCheck)
-- | - FOP shift ops (for finalizeOtherProof)
-- |
-- | Reference: mina/src/lib/pickles/step_main.ml (Other_field = Step.Other_field)
module Pickles.Step.OtherField
  ( StepOtherField
  , fopShiftOps
  , ipaScalarOps
  ) where

import Pickles.ShiftOps (FopShiftOps, IpaScalarOps)
import Safe.Coerce (coerce)
import Snarky.Circuit.DSL (class CircuitM, Bool(..), BoolVar, FVar, equals_)
import Snarky.Circuit.Kimchi (SplitField(..), Type1, Type2(..), fromShiftedSplitFieldCircuit, fromShiftedType1Circuit, scaleFast2, shiftedEqualType1)
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Curves.Class (class FieldSizeInBits)

-- | Step circuit's FOP cross-field variable type.
-- | Represents Fq deferred values using Type1 shift (2*t + 2^n + 1),
-- | matching OCaml's Shifted_value.Type1 for the Step FOP.
type StepOtherField f = Type1 f

-- | IPA scalar ops for the Step circuit.
-- |
-- | Used by checkBulletproof and ipaFinalCheck when verifying Wrap proofs
-- | in the Step circuit. Scalars (z1, z2, CIP, b) are Fq values that need
-- | the SplitField representation.
-- |
-- | Replaces the old `type2ScalarOps` from IPA.purs.
ipaScalarOps
  :: forall f t m
   . FieldSizeInBits f 255
  => CircuitM f (KimchiConstraint f) t m
  => IpaScalarOps f t m (Type2 (SplitField (FVar f) (BoolVar f)))
ipaScalarOps =
  { scaleByShifted: \p (Type2 (SplitField t)) -> scaleFast2 @51 @254 p t
  , shiftedToAbsorbFields: \(Type2 (SplitField { sDiv2, sOdd })) -> [ sDiv2, coerce sOdd ]
  , unshift: \(Type2 sf) -> fromShiftedSplitFieldCircuit sf
  , shiftedEqual: \(Type2 sf) raw -> equals_ (fromShiftedSplitFieldCircuit sf) raw
  }

-- | FOP shift ops for the Step circuit's finalizeOtherProof.
-- |
-- | These are the unshift/shiftedEqual operations needed by the Step FOP
-- | to verify deferred values from previous Wrap proofs.
-- | Uses Type1 shift matching OCaml's Shifted_value.Type1.
fopShiftOps
  :: forall f t m
   . FieldSizeInBits f 255
  => CircuitM f (KimchiConstraint f) t m
  => FopShiftOps f t m (StepOtherField (FVar f))
fopShiftOps =
  { unshift: fromShiftedType1Circuit
  , shiftedEqual: shiftedEqualType1
  }
