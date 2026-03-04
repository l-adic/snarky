-- | Shared type aliases for shifted-value operations used by IPA and FOP circuits.
-- |
-- | These record types bundle the operations needed to work with cross-field
-- | shifted scalar representations (Type1 for Wrap, Type2/SplitField for Step).
-- |
-- | - `IpaScalarOps`: Full set of operations for IPA verification (scale, absorb, unshift, equal)
-- | - `FopShiftOps`: Subset needed by FinalizeOtherProof (unshift, equal)
module Pickles.ShiftOps
  ( IpaScalarOps
  , FopShiftOps
  ) where

import Snarky.Circuit.DSL (BoolVar, FVar, Snarky)
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Data.EllipticCurve (AffinePoint)

-- | Operations for working with shifted scalar values in the IPA circuit.
-- |
-- | This record bundles operations that depend on the specific shifted type
-- | (Type1 for Vesta scalars in Pallas circuits, Type2 for Pallas scalars in Vesta circuits).
-- |
-- | Parameters:
-- | - `f`: base field type (Pallas.BaseField or Vesta.BaseField)
-- | - `t`: tag type
-- | - `m`: underlying monad
-- | - `sf`: shifted scalar type (Type1 (FVar f) or SplitField (FVar f) (BoolVar f))
type IpaScalarOps f t m sf =
  { -- | Scale a curve point by a shifted scalar value.
    -- | This corresponds to `scale_fast` in wrap_verifier.ml.
    scaleByShifted ::
      AffinePoint (FVar f)
      -> sf
      -> Snarky (KimchiConstraint f) t m (AffinePoint (FVar f))
  , -- | Get the field elements to absorb for a shifted scalar.
    -- | For Type1: returns [t] (single field element)
    -- | For Type2: returns [sDiv2, if sOdd then 1 else 0] (two elements)
    shiftedToAbsorbFields ::
      sf
      -> Array (FVar f)
  , -- | Recover the original field element from a shifted representation.
    -- | For Type1: s = 2*t + 2^n + 1
    -- | For Type2: s = 2*sDiv2 + sOdd + 2^n
    unshift ::
      sf
      -> FVar f
  , -- | Compare a claimed shifted value against a raw computed value.
    -- | Uses the of_field convention (shift the raw value, compare inners)
    -- | to match OCaml's Shifted_value.equal.
    shiftedEqual ::
      sf
      -> FVar f
      -> Snarky (KimchiConstraint f) t m (BoolVar f)
  }

-- | Subset of shift operations needed by FinalizeOtherProof circuits.
-- |
-- | Both Step and Wrap FOP need only `unshift` and `shiftedEqual` to verify
-- | deferred values (combined_inner_product, b, perm).
type FopShiftOps f t m sf =
  { unshift :: sf -> FVar f
  , shiftedEqual :: sf -> FVar f -> Snarky (KimchiConstraint f) t m (BoolVar f)
  }
