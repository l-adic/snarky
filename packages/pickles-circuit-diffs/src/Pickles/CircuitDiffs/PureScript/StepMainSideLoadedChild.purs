module Pickles.CircuitDiffs.PureScript.StepMainSideLoadedChild
  ( compileStepMainSideLoadedChild
  , StepMainSideLoadedChildParams
  ) where

-- | step_main circuit for the side-loaded CHILD (No_recursion + dummy_constraints).
-- |
-- | Reference: mina/src/lib/crypto/pickles/dump_side_loaded_main/dump_side_loaded_main.ml:75-96
-- |   (the inner `No_recursion` rule whose proof gets verified by the
-- |   side-loaded parent in `Simple_chain`).
-- |
-- | OCaml fixture target: `step_main_side_loaded_child_circuit.json`
-- | produced by the `step_main_side_loaded_child` entry in
-- | `mina/src/lib/crypto/pickles/dump_circuit_impl.ml`.
-- |
-- | The `dummy_constraints` body translates OCaml
-- | `dump_side_loaded_main.ml:49-73` 1:1: an `exists`-allocated scalar
-- | `x`, an inner-curve generator `g` (allocated via
-- | `WeierstrassAffinePoint` so on-curve check fires), then four
-- | gate-emitting calls — `toFieldChecked' @1`, `scaleFast1 @1 @5` ×2,
-- | `endo @4 @1` — and a final `StepField.Assert.equal self StepField.zero`.
-- | Byte-identical to OCaml (PS=OCaml=447 gates).

import Prelude

import Data.Maybe (Maybe(..), fromJust)
import Data.Vector as Vector
import Effect (Effect)
import Effect.Ref as Ref
import Partial.Unsafe (unsafePartial)
import Pickles.CircuitDiffs.PureScript.Common (StepArtifact, dummyWrapSg, mkStepArtifact)
import Pickles.Field (StepField)
import Pickles.Step.Advice (StepAdvice)
import Pickles.Step.Main (RuleOutput, stepMain)
import Run as Run
import Snarky.Backend.Compile (compile)
import Snarky.Circuit.DSL (AsProver, F(..), FVar, SizedF, Snarky, assertEqual_, const_, exists)
import Snarky.Circuit.Kimchi.EndoMul (endo)
import Snarky.Circuit.Kimchi.EndoScalar (toFieldChecked')
import Snarky.Circuit.Kimchi.VarBaseMul (scaleFast1)
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Constraint.Kimchi as Kimchi
import Snarky.Curves.Class (class PrimeField, fromInt, generator, toAffine)
import Snarky.Curves.Pasta (PallasG)
import Snarky.Data.EllipticCurve (AffinePoint(..), WeierstrassAffinePoint(..))
import Snarky.Types.Shifted (Type1(..))
import Type.Proxy (Proxy(..))
import Unsafe.Coerce (unsafeCoerce)

type StepMainSideLoadedChildParams =
  { blindingH :: AffinePoint (F StepField)
  }

-- | Pallas generator's affine coordinates as an `F StepField` pair.
-- | Mirrors OCaml `Backend.Tick.Inner_curve.(to_affine_exn one)` (the
-- | Pallas generator). Coordinates are over `Pallas.BaseField =
-- | Vesta.ScalarField = StepField`.
innerCurveGen :: { x :: F StepField, y :: F StepField }
innerCurveGen =
  let
    { x, y } = unsafePartial $ fromJust $ toAffine (generator :: PallasG)
  in
    { x: F x, y: F y }

-- | Side-loaded child rule body. Mirrors
-- | dump_side_loaded_main.ml:87-94's [No_recursion] rule:
-- |   dummy_constraints () ;
-- |   StepField.Assert.equal self StepField.zero ;
-- |   { previous_proof_statements = [] ; public_output = () ; ... }
sideLoadedChildRule
  :: forall r
   . PrimeField StepField
  => AsProver StepField r Unit
  -> FVar StepField
  -> Snarky StepField (KimchiConstraint StepField) r
       (RuleOutput 0 Unit Unit)
sideLoadedChildRule _ appState = do
  -- dummy_constraints body — translation of OCaml
  -- dump_side_loaded_main.ml:49-73.
  -- (1) `let x = exists StepField.typ ~compute:(fun () -> 3)`
  x <- exists (pure (F (fromInt 3) :: F StepField))
  -- (2) `let g = exists Step_main_inputs.Inner_curve.typ ~compute:(...)`
  --     Allocate as WeierstrassAffinePoint so `exists` triggers
  --     assert_on_curve (matching OCaml's Inner_curve.typ).
  WeierstrassAffinePoint g :: WeierstrassAffinePoint PallasG (FVar StepField) <-
    exists (pure (WeierstrassAffinePoint innerCurveGen))
  -- (3) `Scalar_challenge.to_field_checked' ~num_bits:16 (SC.create x)`.
  --     Emits a single EC_endoscalar (EndoMulScalar) gate over the
  --     16-bit scalar `x` and discards the (a, b, n) accumulators.
  --     `@rows = 1` (rows = 16 bits / 16 bits-per-row).
  _ <- toFieldChecked' @1 (unsafeCoerce x :: SizedF 16 (FVar StepField))
  -- (4) `Step_main_inputs.Ops.scale_fast g ~num_bits:5 (Shifted_value x)` ×2.
  --     OCaml's `Step_main_inputs.Ops.scale_fast` is the Type1 `scale_fast`
  --     (`Plonk_curve_ops.Make(Step.Impl)(Step_main_inputs.Inner_curve).scale_fast`).
  --     PS counterpart: `scaleFast1 @nChunks @bitsUsed g (Type1 x)` with
  --     `Mul 5 nChunks bitsUsed` ⇒ for `~num_bits:5` use `@1 @5`.
  _ <- scaleFast1 @1 @5 (AffinePoint g) (Type1 x)
  _ <- scaleFast1 @1 @5 (AffinePoint g) (Type1 x)
  -- (5) `Step_verifier.Scalar_challenge.endo g ~num_bits:4 (SC.create x)`.
  --     Parameterized `endo @nBits @rows` (Mul 4 rows nBits) — for
  --     num_bits=4 use `@4 @1` (a single 4-bit chunk).
  _ <- endo @4 @1 (AffinePoint g) (unsafeCoerce x :: SizedF 4 (FVar StepField))

  -- `StepField.Assert.equal self StepField.zero`
  assertEqual_ appState (const_ zero)
  pure
    { prevPublicInputs: Vector.nil
    , proofMustVerify: Vector.nil
    , publicOutput: unit
    }

compileStepMainSideLoadedChild
  :: StepMainSideLoadedChildParams -> Effect StepArtifact
compileStepMainSideLoadedChild params = do
  throwawayCaptureRef <- Ref.new Nothing
  -- `carrier` (value-side per-proof witness carrier) is not determined
  -- by `stepMain`'s var-side `StepSlotsCarrier` constraint; pin it here
  -- (mpv=0 ⇒ empty `Unit` carrier).
  let
    dummyAdvice :: StepAdvice _ _ _ _ _ _ Unit _ _
    dummyAdvice = unsafeCoerce unit
  mkStepArtifact <$> Run.runBaseEffect do
    compile (Proxy @Unit) (Proxy @(Vector.Vector 1 (F StepField)))
      (Proxy @(KimchiConstraint StepField))
      -- N=0, Input mode (input is the rule's `self` field). Output is
      -- Unit. Single-rule, no prevs ⇒ mpvMax=0, mpvPad=0,
      -- outputSize = mpvMax*32+1+mpvMax = 1 (just the msgForNextStep
      -- digest — no unfinalized_proofs, no msgs_wrap entries).
      -- Visible axes: @prevsSpec @inputVal @outputVal @prevInputVal
      -- @valCarrier @mpvMax @nd. Implicit: input/output/prevInput
      -- (CircuitType funcdep), mpvPad (MpvPadding), outputSize
      -- (Mul/Add chain).
      ( \_ -> stepMain
          @Unit
          @(F StepField)
          @Unit
          @Unit
          @Unit
          @0
          @1
          @Unit
          @1
          sideLoadedChildRule
          { perSlotLagrangeAt: Vector.nil
          , blindingH: params.blindingH
          , perSlotFopDomainLog2s: Vector.nil
          , perSlotVkBlueprints: unit
          }
          dummyWrapSg
          unit
          dummyAdvice
          throwawayCaptureRef
      )
