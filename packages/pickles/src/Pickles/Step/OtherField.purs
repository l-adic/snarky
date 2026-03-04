-- | Step circuit's cross-field representation.
-- |
-- | The Step circuit operates over Fp (Vesta.ScalarField). The "other field" is
-- | Fq (Pallas.ScalarField), which is LARGER than Fp. Values from Fq are
-- | represented as SplitField { sDiv2 :: FVar f, sOdd :: BoolVar f } with an
-- | implicit 2^n shift: s = 2*sDiv2 + sOdd + 2^n.
-- |
-- | This module provides:
-- | - Type aliases for the Step circuit's cross-field representation
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
import Snarky.Circuit.Kimchi (SplitField(..), Type2(..), fromShiftedSplitFieldCircuit, scaleFast2)
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Curves.Class (class FieldSizeInBits)

-- | Step circuit's cross-field variable type.
-- | Represents Fq values (from the other curve) split as (sDiv2, sOdd)
-- | with a 2^n shift, wrapped in Type2 for explicit shift semantics
-- | and forbidden value checks via CheckedType.
type StepOtherField f b = Type2 (SplitField f b)

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
  => IpaScalarOps f t m (StepOtherField (FVar f) (BoolVar f))
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
fopShiftOps
  :: forall f t m
   . FieldSizeInBits f 255
  => CircuitM f (KimchiConstraint f) t m
  => FopShiftOps f t m (StepOtherField (FVar f) (BoolVar f))
fopShiftOps =
  { unshift: \(Type2 sf) -> fromShiftedSplitFieldCircuit sf
  , shiftedEqual: \(Type2 sf) raw -> equals_ (fromShiftedSplitFieldCircuit sf) raw
  }
