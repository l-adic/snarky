module Pickles.CircuitDiffs.PureScript.StepMainSideLoadedChild
  ( compileStepMainSideLoadedChild
  , StepMainSideLoadedChildParams
  , class SideLoadedChildAdvice
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
-- | `endo @4 @1` — and a final `Field.Assert.equal self Field.zero`.
-- | Byte-identical to OCaml (PS=OCaml=447 gates).

import Prelude

import Data.Maybe (fromJust)
import Data.Vector as Vector
import Effect (Effect)
import Partial.Unsafe (unsafePartial)
import Pickles.CircuitDiffs.PureScript.Common (StepArtifact, dummyWrapSg, mkStepArtifact)
import Pickles.Step.Main (RuleOutput, stepMain)
import Pickles.Step.Prevs (PrevsSpecNil)
import Pickles.Types (StepField)
import Snarky.Backend.Compile (compile)
import Snarky.Circuit.DSL (class CircuitM, F(..), FVar, SizedF, Snarky, assertEqual_, const_, exists)
import Snarky.Circuit.Kimchi.EndoMul (endo)
import Snarky.Circuit.Kimchi.EndoScalar (toFieldChecked')
import Snarky.Circuit.Kimchi.VarBaseMul (scaleFast1)
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Constraint.Kimchi as Kimchi
import Snarky.Curves.Class (fromInt, generator, toAffine)
import Snarky.Curves.Pasta (PallasG)
import Snarky.Data.EllipticCurve (AffinePoint, WeierstrassAffinePoint(..))
import Snarky.Types.Shifted (Type1(..))
import Type.Proxy (Proxy(..))
import Unsafe.Coerce (unsafeCoerce)

type StepMainSideLoadedChildParams =
  { blindingH :: AffinePoint (F StepField)
  }

-- | Application-specific advice for the side-loaded child rule.
-- |
-- | The rule allocates two witnesses inside `dummy_constraints` (a
-- | scalar `x` and the inner-curve generator `g`); these are pure
-- | constants so the class is empty.
class Monad m <= SideLoadedChildAdvice m

instance (Monad m) => SideLoadedChildAdvice m

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
-- |   Field.Assert.equal self Field.zero ;
-- |   { previous_proof_statements = [] ; public_output = () ; ... }
sideLoadedChildRule
  :: forall t m
   . CircuitM StepField (KimchiConstraint StepField) t m
  => SideLoadedChildAdvice m
  => FVar StepField
  -> Snarky (KimchiConstraint StepField) t m
       (RuleOutput 0 Unit Unit)
sideLoadedChildRule appState = do
  -- dummy_constraints body — translation of OCaml
  -- dump_side_loaded_main.ml:49-73.
  -- (1) `let x = exists Field.typ ~compute:(fun () -> 3)`
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
  _ <- scaleFast1 @1 @5 g (Type1 x)
  _ <- scaleFast1 @1 @5 g (Type1 x)
  -- (5) `Step_verifier.Scalar_challenge.endo g ~num_bits:4 (SC.create x)`.
  --     Parameterized `endo @nBits @rows` (Mul 4 rows nBits) — for
  --     num_bits=4 use `@4 @1` (a single 4-bit chunk).
  _ <- endo @4 @1 g (unsafeCoerce x :: SizedF 4 (FVar StepField))

  -- `Field.Assert.equal self Field.zero`
  assertEqual_ appState (const_ zero)
  pure
    { prevPublicInputs: Vector.nil
    , proofMustVerify: Vector.nil
    , publicOutput: unit
    }

compileStepMainSideLoadedChild
  :: StepMainSideLoadedChildParams -> Effect StepArtifact
compileStepMainSideLoadedChild params =
  mkStepArtifact <$>
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
          @PrevsSpecNil
          @(F StepField)
          @Unit
          @Unit
          @Unit
          @0
          @1
          sideLoadedChildRule
          { perSlotLagrangeAt: Vector.nil
          , blindingH: params.blindingH
          , perSlotFopDomainLog2s: Vector.nil
          , perSlotVkSources: Vector.nil
          }
          dummyWrapSg
          unit
      )
      Kimchi.initialState
