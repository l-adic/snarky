-- | Wrap circuit's cross-field representation.
-- |
-- | The Wrap circuit operates over Fq (Pallas.ScalarField). The "other field" is
-- | Fp (Vesta.ScalarField), which is SMALLER than Fq. Values from Fp fit in a
-- | single field element, represented as Type1 (FVar f) with shift 2*t + 2^n + 1.
-- |
-- | This module provides:
-- | - Type aliases for the Wrap circuit's cross-field representation
-- | - IPA scalar ops (for checkBulletproof / ipaFinalCheck)
-- | - FOP shift ops (for wrapFinalizeOtherProof)
-- |
-- | Reference: mina/src/lib/pickles/wrap_main.ml (Other_field = Wrap.Other_field)
module Pickles.Wrap.OtherField
  ( WrapOtherField
  , ipaScalarOps
  , fopShiftOps
  ) where

import Prelude

import Pickles.ShiftOps (IpaScalarOps)
import Snarky.Circuit.DSL (class CircuitM, BoolVar, FVar, Snarky, seal)
import Snarky.Circuit.Kimchi (Type1(..), Type2(..), fromShiftedType1Circuit, fromShiftedType2Circuit, scaleFast1, shiftedEqualType1, shiftedEqualType2)
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Curves.Class (class FieldSizeInBits)

-- | Wrap circuit's cross-field variable type for IPA.
-- | Represents Fp values (from the other curve) as a single field element
-- | with Type1 shift: s = 2*t + 2^n + 1.
type WrapOtherField f = Type1 f

-- | IPA scalar ops for the Wrap circuit.
-- |
-- | Used by checkBulletproof and ipaFinalCheck when verifying Step proofs
-- | in the Wrap circuit. Scalars (z1, z2, CIP, b) are Fp values that fit
-- | in the single-element Type1 representation.
-- |
-- | Replaces the old `type1ScalarOps` from IPA.purs.
ipaScalarOps
  :: forall f t m
   . FieldSizeInBits f 255
  => CircuitM f (KimchiConstraint f) t m
  => IpaScalarOps f t m (WrapOtherField (FVar f))
ipaScalarOps =
  { scaleByShifted: \p t -> scaleFast1 @51 p t
  , shiftedToAbsorbFields: \(Type1 t) -> [ t ]
  , unshift: fromShiftedType1Circuit
  , shiftedEqual: shiftedEqualType1
  }

-- | FOP shift ops for the Wrap circuit's finalizeOtherProof.
-- |
-- | The Wrap FOP uses Type2 shift (x + 2^n) for deferred values,
-- | matching OCaml's Shifted_value.Type2.
-- |
-- | The sealInner operation is needed for map_plonk_to_field in Wrap FOP.
fopShiftOps
  :: forall @f t @m
   . FieldSizeInBits f 255
  => CircuitM f (KimchiConstraint f) t m
  => { unshift :: Type2 (FVar f) -> FVar f
     , shiftedEqual :: Type2 (FVar f) -> FVar f -> Snarky (KimchiConstraint f) t m (BoolVar f)
     , sealInner :: Type2 (FVar f) -> Snarky (KimchiConstraint f) t m (Type2 (FVar f))
     }
fopShiftOps =
  { unshift: fromShiftedType2Circuit
  , shiftedEqual: shiftedEqualType2
  , sealInner: \(Type2 x) -> Type2 <$> seal x
  }
