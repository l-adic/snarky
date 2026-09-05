module Pickles.CircuitDiffs.PureScript.CheckBulletproofWrap
  ( parseCheckBulletproofWrapInput
  , checkBulletproofWrapCircuit
  , compileCheckBulletproofWrap
  ) where

import Prelude

import Data.Fin (getFinite, unsafeFinite)
import Data.Maybe (Maybe(..))
import Data.Vector (Vector)
import Data.Vector as Vector
import Effect (Effect)
import Pickles.CircuitDiffs.PureScript.Common (CompiledCircuit, asSizedF128, unsafeIdx, wrapEndo)
import Pickles.Field (WrapField)
import Pickles.IPA (checkBulletproof)
import Pickles.Sponge (evalSpongeM)
import Pickles.Wrap.OtherField as WrapOtherField
import RandomOracle.Sponge (SpongeState(..))
import Safe.Coerce (coerce)
import Snarky.Backend.Advice (noAdvice)
import Snarky.Backend.Compile (compile)
import Snarky.Circuit.DSL (Bool(..), BoolVar, F(..), FVar, SizedF, Snarky, const_)
import Snarky.Circuit.Kimchi (Type1(..), groupMapParams)
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Curves.Class (class PrimeField)
import Snarky.Curves.Pasta (VestaG)
import Snarky.Data.EllipticCurve (AffinePoint(..))
import Type.Proxy (Proxy(..))

-- | The `check_bulletproof_wrap_circuit` input: the sponge state at
-- | `sponge_before_evaluations` (mode `Squeezed 1`) at 0-2, `xi` at 3, the two mask bits at 4-5, two
-- | `sg_old` points at 6-9, `x_hat` at 10-11, `ft_comm` at 12-13, `z_comm` at 14-15, the six index
-- | commitments at 16-27, the 15 `w_comm` at 28-57, the 15 coefficient commitments at 58-87,
-- | the six `sigma_comm` at 88-99, the 16 `(L, R)` pairs at 100-163, `delta` at 164, `sg` at
-- | 166, then the Type1-shifted scalars `z1`, `z2`, `cip`, `b` at 168-171.
type CheckBulletproofWrapInput =
  { sponge :: Vector 3 (FVar WrapField)
  , xi :: SizedF 128 (FVar WrapField)
  , masks :: Vector 47 (Maybe (BoolVar WrapField))
  , bases :: Vector 47 (AffinePoint (FVar WrapField))
  , delta :: AffinePoint (FVar WrapField)
  , sg :: AffinePoint (FVar WrapField)
  , lr :: Vector 16 { l :: AffinePoint (FVar WrapField), r :: AffinePoint (FVar WrapField) }
  , z1 :: Type1 (FVar WrapField)
  , z2 :: Type1 (FVar WrapField)
  , combinedInnerProduct :: Type1 (FVar WrapField)
  , b :: Type1 (FVar WrapField)
  }

parseCheckBulletproofWrapInput :: Vector 172 (FVar WrapField) -> CheckBulletproofWrapInput
parseCheckBulletproofWrapInput inputs =
  let
    at = unsafeIdx inputs
    readPt i = AffinePoint { x: at i, y: at (i + 1) }
    readShifted i = Type1 (at i)
    -- `sg_old` ×2, `x_hat`, `ft_comm`, `z_comm`, index ×6, `w_comm` ×15, coefficients ×15, `sigma` ×6
    basePts = Vector.generate \j -> readPt (6 + 2 * getFinite j)
  in
    { sponge: Vector.generate \j -> at (getFinite j)
    , xi: asSizedF128 (at 3)
    , masks: Vector.generate \j -> if getFinite j < 2 then Just (coerce (at (4 + getFinite j))) else Nothing
    , bases: basePts
    , lr: Vector.generate \j ->
        { l: readPt (100 + 4 * getFinite j), r: readPt (100 + 4 * getFinite j + 2) }
    , delta: readPt 164
    , sg: readPt 166
    , z1: readShifted 168
    , z2: readShifted 169
    , combinedInnerProduct: readShifted 170
    , b: readShifted 171
    }

-- | The library gadget `Pickles.IPA.checkBulletproof` on the wrap side, from the given
-- | squeezed sponge; the success bit and the challenges are left unasserted, as the
-- | gadget returns them.
checkBulletproofWrapCircuit
  :: forall r
   . PrimeField WrapField
  => AffinePoint (F WrapField)
  -> CheckBulletproofWrapInput
  -> Snarky WrapField (KimchiConstraint WrapField) r Unit
checkBulletproofWrapCircuit blindingH input = do
  let
    AffinePoint { x: F hx, y: F hy } = blindingH
    params = { endo: const_ wrapEndo, groupMapParams: groupMapParams (Proxy @VestaG) }
    sponge = { state: input.sponge, spongeState: Squeezed (unsafeFinite @3 1) }
  _ <- evalSpongeM sponge $
    checkBulletproof @WrapField @VestaG WrapOtherField.ipaScalarOps params input.bases input.masks
      { xi: input.xi
      , delta: input.delta
      , sg: input.sg
      , lr: input.lr
      , z1: input.z1
      , z2: input.z2
      , combinedInnerProduct: input.combinedInnerProduct
      , b: input.b
      , blindingGenerator: AffinePoint { x: const_ hx, y: const_ hy }
      }
  pure unit

compileCheckBulletproofWrap :: AffinePoint (F WrapField) -> Effect (CompiledCircuit WrapField)
compileCheckBulletproofWrap blindingH =
  compile noAdvice (Proxy @(Vector 172 (F WrapField))) (Proxy @Unit) (Proxy @(KimchiConstraint WrapField))
    (\inputs -> checkBulletproofWrapCircuit blindingH (parseCheckBulletproofWrapInput inputs))
