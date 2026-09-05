module Pickles.CircuitDiffs.PureScript.CheckBulletproofStep
  ( parseCheckBulletproofStepInput
  , checkBulletproofStepCircuit
  , compileCheckBulletproofStep
  ) where

import Prelude

import Data.Fin (getFinite, unsafeFinite)
import Data.Maybe (Maybe(..))
import Data.Vector (Vector)
import Data.Vector as Vector
import Effect (Effect)
import Pickles.CircuitDiffs.PureScript.Common (CompiledCircuit, asSizedF128, stepEndo, unsafeIdx)
import Pickles.Field (StepField)
import Pickles.IPA (checkBulletproof)
import Pickles.Sponge (evalSpongeM)
import Pickles.Step.OtherField as StepOtherField
import RandomOracle.Sponge (SpongeState(..))
import Safe.Coerce (coerce)
import Snarky.Backend.Advice (noAdvice)
import Snarky.Backend.Compile (compile)
import Snarky.Circuit.DSL (Bool(..), BoolVar, F(..), FVar, SizedF, Snarky, const_)
import Snarky.Circuit.Kimchi (SplitField(..), Type2(..), groupMapParams)
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Curves.Class (class PrimeField)
import Snarky.Curves.Pasta (PallasG)
import Snarky.Data.EllipticCurve (AffinePoint(..))
import Type.Proxy (Proxy(..))

-- | The `check_bulletproof_step_circuit` input: the sponge state at
-- | `sponge_before_evaluations` (mode `Squeezed 1`) at 0-2, `xi` at 3, two
-- | `sg_old` points at 4-7, `x_hat` at 8-9, `ft_comm` at 10-11, `z_comm` at 12-13, the six index
-- | commitments at 14-25, the 15 `w_comm` at 26-55, the 15 coefficient commitments at 56-85,
-- | the six `sigma_comm` at 86-97, the 15 `(L, R)` pairs at 98-157, `delta` at 158, `sg` at
-- | 160, then the Type2-shifted (two fields each) scalars `z1`, `z2`, `cip`, `b` at 162-169.
type CheckBulletproofStepInput =
  { sponge :: Vector 3 (FVar StepField)
  , xi :: SizedF 128 (FVar StepField)
  , masks :: Vector 47 (Maybe (BoolVar StepField))
  , bases :: Vector 47 (AffinePoint (FVar StepField))
  , delta :: AffinePoint (FVar StepField)
  , sg :: AffinePoint (FVar StepField)
  , lr :: Vector 15 { l :: AffinePoint (FVar StepField), r :: AffinePoint (FVar StepField) }
  , z1 :: Type2 (SplitField (FVar StepField) (BoolVar StepField))
  , z2 :: Type2 (SplitField (FVar StepField) (BoolVar StepField))
  , combinedInnerProduct :: Type2 (SplitField (FVar StepField) (BoolVar StepField))
  , b :: Type2 (SplitField (FVar StepField) (BoolVar StepField))
  }

parseCheckBulletproofStepInput :: Vector 170 (FVar StepField) -> CheckBulletproofStepInput
parseCheckBulletproofStepInput inputs =
  let
    at = unsafeIdx inputs
    readPt i = AffinePoint { x: at i, y: at (i + 1) }
    readShifted i = Type2 (SplitField { sDiv2: at i, sOdd: coerce (at (i + 1)) })
    -- `sg_old` ×2, `x_hat`, `ft_comm`, `z_comm`, index ×6, `w_comm` ×15, coefficients ×15, `sigma` ×6
    basePts = Vector.generate \j -> readPt (4 + 2 * getFinite j)
  in
    { sponge: Vector.generate \j -> at (getFinite j)
    , xi: asSizedF128 (at 3)
    , masks: Vector.replicate Nothing
    , bases: basePts
    , lr: Vector.generate \j ->
        { l: readPt (98 + 4 * getFinite j), r: readPt (98 + 4 * getFinite j + 2) }
    , delta: readPt 158
    , sg: readPt 160
    , z1: readShifted 162
    , z2: readShifted 164
    , combinedInnerProduct: readShifted 166
    , b: readShifted 168
    }

-- | The library gadget `Pickles.IPA.checkBulletproof` on the step side, from the given
-- | squeezed sponge; the success bit and the challenges are left unasserted, as the
-- | gadget returns them.
checkBulletproofStepCircuit
  :: forall r
   . PrimeField StepField
  => AffinePoint (F StepField)
  -> CheckBulletproofStepInput
  -> Snarky StepField (KimchiConstraint StepField) r Unit
checkBulletproofStepCircuit blindingH input = do
  let
    AffinePoint { x: F hx, y: F hy } = blindingH
    params = { endo: const_ stepEndo, groupMapParams: groupMapParams (Proxy @PallasG) }
    sponge = { state: input.sponge, spongeState: Squeezed (unsafeFinite @3 1) }
  _ <- evalSpongeM sponge $
    checkBulletproof @StepField @PallasG StepOtherField.ipaScalarOps params input.bases input.masks
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

compileCheckBulletproofStep :: AffinePoint (F StepField) -> Effect (CompiledCircuit StepField)
compileCheckBulletproofStep blindingH =
  compile noAdvice (Proxy @(Vector 170 (F StepField))) (Proxy @Unit) (Proxy @(KimchiConstraint StepField))
    (\inputs -> checkBulletproofStepCircuit blindingH (parseCheckBulletproofStepInput inputs))
