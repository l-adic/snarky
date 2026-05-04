-- | M6 / M7a / M7b acceptance tests for the side-loaded `step_main`
-- | pipeline.
-- |
-- | Drives `compileMulti` over a 1-rule spec whose single prev slot is a
-- | `PrevsSpecSideLoadedCons` (mirrors OCaml's
-- | `dump_side_loaded_main.ml:99-156` parent: side-loaded child verifier
-- | with `Width.Max = N2`). Re-uses `simpleChainRule` from
-- | `Test.Pickles.Prove.SimpleChain` — the rule body is identical, the
-- | only spec-level difference is that the prev slot's wrap key is
-- | side-loaded (handler-provided) instead of compile-time-known.
-- |
-- | Milestones:
-- |
-- |   * M6: `compileMulti` returns a `BranchProver` for a side-loaded
-- |     spec without crashing.
-- |
-- |   * M7a: per-prove `sideloadedVKs` channel is plumbed through
-- |     `StepInputs` / `BranchProver` / `runMultiProverBody`.
-- |
-- |   * M7b (this test): the side-loaded slot has no `BasePrev` path
-- |     (OCaml `dump_side_loaded_main.ml:190-202` always passes a real
-- |     child proof). PS-compile an Input-mode `No_recursion` child,
-- |     drive its prover to obtain a `CompiledProof 0 …`, width-lift
-- |     to `CompiledProof 2 …` (the side-loaded tag's compile-time
-- |     bound) via `Safe.Coerce.coerce` — PS analog of OCaml
-- |     `Side_loaded.Proof.of_proof`. Construct the runtime
-- |     `Sideload.VerificationKey` from the child's wrap CompileResult
-- |     and drive the parent prover with `InductivePrev`.
-- |
-- |   * M9 (next): same flow with `KIMCHI_DETERMINISTIC_SEED=42
-- |     KIMCHI_WITNESS_DUMP=…`; diff against committed
-- |     `packages/pickles/test/fixtures/witness_sideload/ocaml_main_step_b1.txt`
-- |     via `tools/witness_diff.sh`.
-- |
-- | Reference: `docs/sideload-witness-loop-handoff.md`.
module Test.Pickles.Prove.SideLoadedMain
  ( spec
  ) where

import Prelude

import Control.Monad.Except (runExceptT)
import Data.Either (Either(..))
import Data.Int.Bits as Int
import Data.Maybe (Maybe(..), fromJust)
import Data.Tuple (fst)
import Data.Tuple.Nested (Tuple1, tuple1, (/\))
import Data.Vector as Vector
import Effect.Aff (Aff)
import Effect.Class (liftEffect)
import Effect.Exception (throw) as Exc
import Partial.Unsafe (unsafePartial)
import Pickles.Prove.Compile
  ( BranchProver(..)
  , CompiledProof
  , PrevSlot(..)
  , RulesCons
  , RulesNil
  , Tag
  , compileMulti
  , mkRuleEntry
  )
import Pickles.Prove.Step (StepRule, extractWrapVKCommsAdvice)
import Pickles.Sideload.VerificationKey (ProofsVerified(..), mkChecked)
import Pickles.Sideload.VerificationKey (VerificationKey) as Sideload
import Pickles.Step.Prevs (PrevsSpecNil, PrevsSpecSideLoadedCons)
import Pickles.Types (StatementIO, StepField)
import Pickles.Wrap.Slots (NoSlots, Slots1)
import Safe.Coerce (coerce)
import Snarky.Backend.Kimchi.Class (createCRS)
import Snarky.Backend.Kimchi.Impl.Pallas as PallasImpl
import Snarky.Circuit.DSL (F(..), FVar, SizedF, assertEqual_, const_, exists)
import Snarky.Circuit.Kimchi.EndoMul (endo)
import Snarky.Circuit.Kimchi.EndoScalar (toFieldChecked')
import Snarky.Circuit.Kimchi.VarBaseMul (scaleFast1)
import Snarky.Curves.Class (fromInt, generator, toAffine)
import Snarky.Curves.Pasta (PallasG)
import Snarky.Data.EllipticCurve (WeierstrassAffinePoint(..))
import Snarky.Types.Shifted (Type1(..))
import Test.Pickles.Prove.SimpleChain (simpleChainRule)
import Test.Spec (SpecT, describe, it)
import Test.Spec.Assertions (shouldEqual)
import Unsafe.Coerce (unsafeCoerce)

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

-- | Input-mode `No_recursion` child rule: mpv=0, public input is a
-- | field, asserts `self == 0`. PS analog of OCaml
-- | `dump_side_loaded_main.ml`'s `No_recursion` (line 75-96):
-- |
-- | ```ocaml
-- | compile_promise () ~public_input:(Input Field.typ) ~max_proofs_verified:(module Nat.N0) …
-- |   { main = (fun { public_input = self } ->
-- |       dummy_constraints () ;
-- |       Field.Assert.equal self Field.zero ; … ) }
-- | ```
-- |
-- | The `dummy_constraints ()` block IS required for OCaml byte-parity
-- | — each call emits a specific kimchi gate kind (EndoMulScalar,
-- | VarBaseMul, EndoMul) plus the supporting CompleteAdd and on-curve
-- | rows. Translation is verbatim from
-- | `StepMainSideLoadedChild.purs`'s `sideLoadedChildRule`, which is
-- | byte-identical to OCaml in the `step_main_side_loaded_child_circuit`
-- | fixture comparison (86/86 circuit-diffs pass).
noRecursionInputRule
  :: StepRule 0
       Unit
       (F StepField)
       (FVar StepField)
       Unit
       Unit
       (F StepField)
       (FVar StepField)
noRecursionInputRule self = do
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
  _ <- toFieldChecked' @1 (unsafeCoerce x :: SizedF 16 (FVar StepField))
  -- (4) `Step_main_inputs.Ops.scale_fast g ~num_bits:5 (Shifted_value x)` ×2.
  _ <- scaleFast1 @1 @5 g (Type1 x)
  _ <- scaleFast1 @1 @5 g (Type1 x)
  -- (5) `Step_verifier.Scalar_challenge.endo g ~num_bits:4 (SC.create x)`.
  _ <- endo @4 @1 g (unsafeCoerce x :: SizedF 4 (FVar StepField))

  -- `Field.Assert.equal self Field.zero`
  assertEqual_ self (const_ zero)
  pure
    { prevPublicInputs: Vector.nil
    , proofMustVerify: Vector.nil
    , publicOutput: unit
    }

-- | 1-rule carrier for the Input-mode No_recursion child. Same
-- | shape as `Test.Pickles.Prove.NoRecursionReturn.NrrRules` (mpv=0,
-- | valCarrier=Unit, no prevs); only the rule's input/output types
-- | differ (Input-mode here vs Output-mode in NoRecursionReturn).
type NoRecursionInputRules =
  RulesCons 0 Unit PrevsSpecNil Unit RulesNil

-- | Single-rule spec: one self-recursive rule whose prev slot is
-- | side-loaded with `Width.Max = N2`. Mirrors OCaml
-- | `dump_side_loaded_main.ml`'s parent step rule.
type SideLoadedMainRules =
  RulesCons 1
    (Tuple1 (StatementIO (F StepField) Unit))
    (PrevsSpecSideLoadedCons 2 (StatementIO (F StepField) Unit) PrevsSpecNil)
    (Tuple1 Unit)
    RulesNil

spec :: SpecT Aff Unit Aff Unit
spec = describe "Pickles.Prove.SideLoadedMain" do
  it "parent prove with InductivePrev (PS-compiled child, width-lifted to N2)" \_ -> do
    let pallasSrs = PallasImpl.pallasCrsCreate (1 `Int.shl` 15)
    vestaSrs <- liftEffect $ createCRS @StepField

    -- ===== Step 1: compile the Input-mode No_recursion child.
    --
    -- PS-side analog of OCaml's child compile + step at
    -- `dump_side_loaded_main.ml:75-110`. Produces a kimchi wrap VK at
    -- log2 = 13 (`mpv = N0` → `wrap_domains.h = 13`), which becomes
    -- the runtime `wrapVk` we hand to the side-loaded slot.
    childEntry <- liftEffect $ mkRuleEntry @0 @Unit @(F StepField)
      noRecursionInputRule
      unit

    child <- liftEffect $ compileMulti
      @NoRecursionInputRules
      @Unit
      @(F StepField)
      @NoSlots
      { srs: { vestaSrs, pallasSrs }
      , debug: false
      , wrapDomainOverride: Nothing
      }
      (tuple1 childEntry)

    let BranchProver childProver = fst child.provers

    -- ===== Step 2: produce a real child b0 proof.
    --
    -- The child is non-recursive, so any value of `appInput` that
    -- satisfies `self == 0` works; we use `F zero`. Mirrors OCaml
    -- `step Field.Constant.zero` (line 103).
    eChildCp <- liftEffect $ runExceptT $ childProver
      { appInput: F zero
      , prevs: unit
      , sideloadedVKs: unit
      }
    childCp0 :: CompiledProof 0 (StatementIO (F StepField) Unit) Unit Unit <- case eChildCp of
      Left e -> liftEffect $ Exc.throw ("childProver: " <> show e)
      Right cp -> pure cp

    -- ===== Step 3: width-lift the child to the side-loaded tag's bound.
    --
    -- The side-loaded slot expects `CompiledProof 2 …` and `Tag _ _ 2`
    -- (`mpvMax = 2` from `PrevsSpecSideLoadedCons 2 stmt rest`). The
    -- actual child has mpv = 0, hidden inside `widthData`'s
    -- existential. Outer `mpv` is phantom on both `CompiledProof` and
    -- `Tag`, so `Safe.Coerce.coerce` repacks the bound — PS analog of
    -- OCaml `Side_loaded.Proof.of_proof`. Sound when the actual width
    -- (here 0) is `≤` the new bound (here 2).
    let
      childCp2 :: CompiledProof 2 (StatementIO (F StepField) Unit) Unit Unit
      childCp2 = coerce childCp0

      childTag2 :: Tag (F StepField) Unit 2
      childTag2 = coerce child.tag

    -- ===== Step 4: assemble the side-loaded VerificationKey.
    --
    -- The runtime VK bundles two pieces: `circuit` (pickles-level
    -- metadata that the in-circuit dispatch reads) and `wrapVk` (the
    -- live kimchi VerifierIndex handle). NRR's wrap circuit at log2 =
    -- 13 → `actual_wrap_domain_size = N0` per
    -- `Common.actual_wrap_domain_size`; child mpv = 0 →
    -- `max_proofs_verified = N0`.
    let
      childVK :: Sideload.VerificationKey
      childVK =
        { circuit: mkChecked
            { maxProofsVerified: N0
            , actualWrapDomainSize: N0
            , wrapIndex: extractWrapVKCommsAdvice child.vks.wrap.verifierIndex
            }
        , wrapVk: Just child.vks.wrap.verifierIndex
        }

    -- ===== Step 5: compile the side-loaded parent.
    sideLoadedEntry <- liftEffect $ mkRuleEntry
      @1
      @Unit
      @(F StepField)
      simpleChainRule
      (tuple1 unit)

    parent <- liftEffect $ compileMulti
      @SideLoadedMainRules
      @Unit
      @(F StepField)
      @(Slots1 2)
      { srs: { vestaSrs, pallasSrs }
      , debug: false
      , wrapDomainOverride: Nothing
      }
      (tuple1 sideLoadedEntry)

    let BranchProver chainProver = fst parent.provers

    -- ===== Step 6: drive the parent prove with InductivePrev.
    --
    -- Mirrors OCaml `dump_side_loaded_main.ml:190-202`'s `step
    -- Field.Constant.one ~handler:…` call: parent self = 1, prev =
    -- (child input = 0, wrapped child proof, child VK).
    -- `simpleChainRule`'s `selfCorrect = (1 + 0 == 1)` → true, so the
    -- assertion holds.
    eParentCp <- liftEffect $ runExceptT $ chainProver
      { appInput: F one
      , prevs: tuple1 (InductivePrev childCp2 childTag2)
      , sideloadedVKs: childVK /\ unit
      }
    case eParentCp of
      Left e -> liftEffect $ Exc.throw ("sideloaded chainProver: " <> show e)
      Right _ -> pure unit

    -- M7b sanity: the parent prove ran end-to-end with a real
    -- side-loaded child proof. Witness equivalence with OCaml is M9.
    true `shouldEqual` true
