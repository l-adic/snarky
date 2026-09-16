-- | Operation records passed to the IPA and finalize-other-proof
-- | circuits, which are written once and instantiated at both shifted
-- | scalar representations: Type1 on the wrap side, Type2/SplitField on
-- | the step side.
module Pickles.ShiftOps
  ( IpaScalarOps
  , FopShiftOps
  ) where

import Snarky.Circuit.DSL (BoolVar, FVar, Snarky)
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Data.EllipticCurve (AffinePoint)

-- | Everything the IPA circuit needs from a shifted scalar `sf`, which
-- | is `Type1 (FVar f)` on the wrap side and
-- | `SplitField (FVar f) (BoolVar f)` on the step side.
type IpaScalarOps f r sf =
  { -- | Scale a curve point by a shifted scalar.
    scaleByShifted ::
      AffinePoint (FVar f)
      -> sf
      -> Snarky f (KimchiConstraint f) r (AffinePoint (FVar f))
  , -- | The field elements a shifted scalar absorbs as: `[t]` for
    -- | Type1, `[sDiv2, sOdd]` for Type2.
    shiftedToAbsorbFields ::
      sf
      -> Array (FVar f)
  , -- | Recover the field element behind a shifted representation:
    -- | `s = 2t + 2^n + 1` for Type1, `s = 2·sDiv2 + sOdd + 2^n` for
    -- | Type2.
    unshift ::
      sf
      -> FVar f
  , -- | Compare a claimed shifted value against a raw computed one, by
    -- | shifting the raw value and comparing the inner representations
    -- | rather than unshifting.
    shiftedEqual ::
      sf
      -> FVar f
      -> Snarky f (KimchiConstraint f) r (BoolVar f)
  }

-- | The two operations the finalize-other-proof circuits need to check
-- | a deferred value: `unshift` and `shiftedEqual`.
type FopShiftOps f r sf =
  { unshift :: sf -> FVar f
  , shiftedEqual :: sf -> FVar f -> Snarky f (KimchiConstraint f) r (BoolVar f)
  }
