module Pickles.CircuitDiffs.PureScript.CheckBulletproofStep
  ( compileCheckBulletproofStep
  ) where

import Prelude

import Data.Fin (reflectFinite)
import Data.Maybe (Maybe(..))
import Data.Tuple.Nested (Tuple10, tuple10, uncurry10)
import Data.Vector (Vector)
import Data.Vector as Vector
import Effect (Effect)
import Pickles.CircuitDiffs.PureScript.Common (CompiledCircuit, stepEndo)
import Pickles.Field (StepField)
import Pickles.IPA (checkBulletproof)
import Pickles.Sponge (evalSpongeM)
import Pickles.Step.OtherField as StepOtherField
import RandomOracle.Sponge (SpongeState(..))
import Snarky.Backend.Advice (noAdvice)
import Snarky.Backend.Compile (compile)
import Snarky.Circuit.DSL (class CircuitType, BoolVar, F(..), FVar, SizedF, Snarky, UnChecked(..), const_, genericFieldsToValue, genericFieldsToVar, genericSizeInFields, genericValueToFields, genericVarToFields)
import Snarky.Circuit.Kimchi (SplitField, Type2, groupMapParams)
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Curves.Pasta (PallasG)
import Snarky.Data.EllipticCurve (AffinePoint(..))
import Type.Proxy (Proxy(..))

-- | `check_bulletproof_step_circuit`'s input (OCaml `dump_circuit_impl.ml`): the sponge state
-- | at `sponge_before_evaluations` (mode `Squeezed 1`), `xi`, the 47 MSM bases (two `sg_old`,
-- | `x_hat`, `ft_comm`, `z_comm`, the six index commitments, the 15 `w_comm`, the 15
-- | coefficient commitments, the six `sigma_comm`), the opening, then the Type2-shifted
-- | deferred `cip` and `b`.
newtype CheckBulletproofStepInput f pt s = CheckBulletproofStepInput
  { sponge :: Vector 3 f
  , xi :: SizedF 128 f
  , bases :: Vector 47 pt
  , lr :: Vector 15 { l :: pt, r :: pt }
  , delta :: pt
  , sg :: pt
  , z1 :: s
  , z2 :: s
  , combinedInnerProduct :: s
  , b :: s
  }

-- | The wire order.
type CheckBulletproofStepTuple f pt s =
  Tuple10 (Vector 3 f) (SizedF 128 f) (Vector 47 pt) (Vector 15 { l :: pt, r :: pt }) pt pt s s s s

toTuple :: forall f pt s. CheckBulletproofStepInput f pt s -> CheckBulletproofStepTuple f pt s
toTuple (CheckBulletproofStepInput i) =
  tuple10 i.sponge i.xi i.bases i.lr i.delta i.sg i.z1 i.z2 i.combinedInnerProduct i.b

fromTuple :: forall f pt s. CheckBulletproofStepTuple f pt s -> CheckBulletproofStepInput f pt s
fromTuple = uncurry10 \sponge xi bases lr delta sg z1 z2 combinedInnerProduct b ->
  CheckBulletproofStepInput { sponge, xi, bases, lr, delta, sg, z1, z2, combinedInnerProduct, b }

instance
  ( CircuitType f fa fv
  , CircuitType f pa pv
  , CircuitType f sa sv
  ) =>
  CircuitType f (CheckBulletproofStepInput fa pa sa) (CheckBulletproofStepInput fv pv sv) where
  sizeInFields pf _ = genericSizeInFields pf (Proxy @(CheckBulletproofStepTuple fa pa sa))
  valueToFields = genericValueToFields <<< toTuple
  fieldsToValue = fromTuple <<< genericFieldsToValue
  varToFields = genericVarToFields @(CheckBulletproofStepTuple fa pa sa) <<< toTuple
  fieldsToVar = fromTuple <<< genericFieldsToVar @(CheckBulletproofStepTuple fa pa sa)

-- | The library gadget `Pickles.IPA.checkBulletproof` on the step side, from the given
-- | squeezed sponge; the success bit and the challenges are left unasserted, as the
-- | gadget returns them.
checkBulletproofStepCircuit
  :: forall r
   . AffinePoint (F StepField)
  -> UnChecked
       ( CheckBulletproofStepInput (FVar StepField) (AffinePoint (FVar StepField))
           (Type2 (SplitField (FVar StepField) (BoolVar StepField)))
       )
  -> Snarky StepField (KimchiConstraint StepField) r Unit
checkBulletproofStepCircuit blindingH (UnChecked (CheckBulletproofStepInput i)) = do
  let
    AffinePoint { x: F hx, y: F hy } = blindingH
    params = { endo: const_ stepEndo, groupMapParams: groupMapParams (Proxy @PallasG) }
    sponge = { state: i.sponge, spongeState: Squeezed (reflectFinite @1) }
  _ <- evalSpongeM sponge $
    checkBulletproof @StepField @PallasG StepOtherField.ipaScalarOps params i.bases
      (Vector.replicate Nothing)
      { xi: i.xi
      , deferred: { combinedInnerProduct: i.combinedInnerProduct, b: i.b }
      , opening: { lr: i.lr, z1: i.z1, z2: i.z2, delta: i.delta, sg: i.sg }
      , blindingGenerator: AffinePoint { x: const_ hx, y: const_ hy }
      }
  pure unit

compileCheckBulletproofStep :: AffinePoint (F StepField) -> Effect (CompiledCircuit StepField)
compileCheckBulletproofStep blindingH =
  compile noAdvice
    ( Proxy
        @( UnChecked
            ( CheckBulletproofStepInput (F StepField) (AffinePoint StepField)
                (Type2 (SplitField (F StepField) Boolean))
            )
        )
    )
    (Proxy @Unit)
    (Proxy @(KimchiConstraint StepField))
    (checkBulletproofStepCircuit blindingH)
