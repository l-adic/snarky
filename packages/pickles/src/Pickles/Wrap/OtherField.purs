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
  ( WrapOtherFieldVar
  , WrapOtherFieldVal
  , ipaScalarOps
  , fopShiftOps
  ) where

import Prelude

import JS.BigInt as BigInt
import Pickles.IPA (IpaScalarOps)
import Snarky.Circuit.DSL (class CircuitM, BoolVar, F, FVar, Snarky, add_, const_, equals_, seal)
import Snarky.Circuit.Kimchi (Type1(..), fromShiftedType1Circuit, scaleFast1, shiftedEqualType1)
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Curves.Class (class FieldSizeInBits, fromBigInt)

-- | Wrap circuit's cross-field variable type.
-- | Represents Fp values (from the other curve) as a single field element
-- | with Type1 shift: s = 2*t + 2^n + 1.
type WrapOtherFieldVar f = Type1 (FVar f)

-- | Wrap circuit's cross-field value type (for witness generation).
type WrapOtherFieldVal f = Type1 (F f)

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
  => IpaScalarOps f t m (WrapOtherFieldVar f)
ipaScalarOps =
  { scaleByShifted: \p t -> scaleFast1 @51 p t
  , shiftedToAbsorbFields: \(Type1 t) -> [ t ]
  , unshift: fromShiftedType1Circuit
  , shiftedEqual: shiftedEqualType1
  }

-- | FOP shift ops for the Wrap circuit's finalizeOtherProof.
-- |
-- | The Wrap FOP uses Type2 shift semantics (x + 2^n) for deferred values,
-- | NOT Type1 shift (2*x + 2^n + 1). This is because OCaml's Wrap.Other_field
-- | uses Shifted_value.Type2.
-- |
-- | The sealInner operation is needed for map_plonk_to_field in Wrap FOP.
fopShiftOps
  :: forall f t m
   . FieldSizeInBits f 255
  => CircuitM f (KimchiConstraint f) t m
  => { unshift :: WrapOtherFieldVar f -> FVar f
     , shiftedEqual :: WrapOtherFieldVar f -> FVar f -> Snarky (KimchiConstraint f) t m (BoolVar f)
     , sealInner :: WrapOtherFieldVar f -> Snarky (KimchiConstraint f) t m (WrapOtherFieldVar f)
     }
fopShiftOps =
  let
    twoTo255 = fromBigInt (BigInt.pow (BigInt.fromInt 2) (BigInt.fromInt 255))
  in
    { unshift: \(Type1 x) -> add_ x (const_ twoTo255)
    , shiftedEqual: \(Type1 claimed) raw -> equals_ (add_ claimed (const_ twoTo255)) raw
    , sealInner: \(Type1 x) -> Type1 <$> seal x
    }
