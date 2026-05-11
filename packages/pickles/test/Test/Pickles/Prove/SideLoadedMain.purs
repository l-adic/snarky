-- | End-to-end test for the side-loaded `step_main` pipeline.
-- |
-- | Drives `compileMulti` over a 1-rule spec whose single prev slot is
-- | a `Slot SideLoaded` (= the prev's wrap key is supplied at
-- | prove time rather than compile time). The test compiles an
-- | Input-mode `No_recursion` child, drives its prover to obtain a
-- | `CompiledProof 0`, width-lifts to the side-loaded tag's bound, and
-- | runs the parent prover with `InductivePrev` against a runtime
-- | `Sideload.VerificationKey` derived from the child's wrap result.
-- |
-- | Reference: OCaml `dump_side_loaded_main.ml`.
module Test.Pickles.Prove.SideLoadedMain
  ( spec
  ) where

import Prelude
import Pickles (BranchProver(..), CompiledProof, compileMulti, getPrevAppStates, mkRuleEntry, NoSlots, PrevSlot(..), ProofsVerified(..), RulesCons, RulesNil, SideLoaded, Slot, Slots1, StatementIO(..), StepField, StepRule, Tag)

import Control.Monad.Except (runExceptT)
import Control.Monad.Trans.Class (lift) as MT
import Data.Either (Either(..))
import Data.Int.Bits as Int
import Data.Maybe (Maybe(..), fromJust)
import Data.Tuple (fst)
import Data.Tuple.Nested (Tuple1, tuple1, (/\))
import Data.Vector ((:<))
import Data.Vector as Vector
import Effect.Aff (Aff)
import Effect.Class (liftEffect)
import Effect.Exception (throw) as Exc
import Partial.Unsafe (unsafePartial)
import Pickles.Sideload.Bundle (Bundle, mkBundle) as Sideload
import Safe.Coerce (coerce)
import Snarky.Backend.Kimchi.Class (createCRS)
import Snarky.Backend.Kimchi.Impl.Pallas as PallasImpl
import Snarky.Circuit.CVar (add_) as CVar
import Snarky.Circuit.DSL (F(..), FVar, SizedF, assertAny_, assertEqual_, const_, equals_, exists, true_)
import Snarky.Circuit.Kimchi.EndoMul (endo)
import Snarky.Circuit.Kimchi.EndoScalar (toFieldChecked')
import Snarky.Circuit.Kimchi.VarBaseMul (scaleFast1)
import Snarky.Curves.Class (fromInt, generator, toAffine)
import Snarky.Curves.Pasta (PallasG)
import Snarky.Data.EllipticCurve (WeierstrassAffinePoint(..))
import Snarky.Types.Shifted (Type1(..))
import Test.Spec (SpecT, describe, it)
import Test.Spec.Assertions (shouldEqual)
import Unsafe.Coerce (unsafeCoerce)

-- | Pallas generator's affine coordinates as `F StepField` (=
-- | `Pallas.BaseField` = `Vesta.ScalarField`).
innerCurveGen :: { x :: F StepField, y :: F StepField }
innerCurveGen =
  let
    { x, y } = unsafePartial $ fromJust $ toAffine (generator :: PallasG)
  in
    { x: F x, y: F y }

-- | Input-mode No_recursion child rule (mpv=0, asserts `self == 0`).
-- | The `dummy_constraints` block emits the gate kinds (EndoMulScalar,
-- | VarBaseMul, EndoMul + on-curve) required for byte-parity with
-- | OCaml's child step CS.
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
  -- dummy_constraints body (= OCaml `dump_side_loaded_main.ml:49-73`).
  x <- exists (pure (F (fromInt 3) :: F StepField))
  -- Allocate `g` as WeierstrassAffinePoint so `exists` triggers
  -- assert_on_curve (matching OCaml's Inner_curve.typ).
  WeierstrassAffinePoint g :: WeierstrassAffinePoint PallasG (FVar StepField) <-
    exists (pure (WeierstrassAffinePoint innerCurveGen))
  _ <- toFieldChecked' @1 (unsafeCoerce x :: SizedF 16 (FVar StepField))
  _ <- scaleFast1 @1 @5 g (Type1 x)
  _ <- scaleFast1 @1 @5 g (Type1 x)
  _ <- endo @4 @1 g (unsafeCoerce x :: SizedF 4 (FVar StepField))
  assertEqual_ self (const_ zero)
  pure
    { prevPublicInputs: Vector.nil
    , proofMustVerify: Vector.nil
    , publicOutput: unit
    }

-- | 1-rule carrier for the Input-mode No_recursion child (mpv=0,
-- | valCarrier=Unit, no prevs).
type NoRecursionInputRules =
  RulesCons 0 Unit Unit Unit RulesNil

-- | 1-rule carrier with a single side-loaded prev slot, `Width.Max = N2`.
type SideLoadedMainRules =
  RulesCons 1
    (Tuple1 (StatementIO (F StepField) Unit))
    (Tuple1 (Slot SideLoaded 2 (StatementIO (F StepField) Unit)))
    (Tuple1 Unit)
    RulesNil

-- | Side-loaded main rule. Asserts `1 + prev == self` OR base case,
-- | with `proofMustVerify = true_` (constant) — required for byte-
-- | parity. A non-constant `proofMustVerify` emits ~25 extra Generic
-- | gates (vanishing under `true_` constant-folding), shifting the
-- | step VK and cascading through the wrap CS's baked `step_keys`
-- | constants. Reference: OCaml `dump_side_loaded_main.ml:179`.
sideLoadedMainRule
  :: StepRule 1
       (Tuple1 (StatementIO (F StepField) Unit))
       (F StepField)
       (FVar StepField)
       Unit
       Unit
       (F StepField)
       (FVar StepField)
sideLoadedMainRule self = do
  prev <- exists $ MT.lift do
    stmt /\ _ <- getPrevAppStates unit
    let StatementIO { input } = stmt
    pure input
  isBaseCase <- equals_ (const_ zero) self
  selfCorrect <- equals_ (CVar.add_ (const_ one) prev) self
  assertAny_ [ selfCorrect, isBaseCase ]
  pure
    { prevPublicInputs: prev :< Vector.nil
    , proofMustVerify: true_ :< Vector.nil
    , publicOutput: unit
    }

spec :: SpecT Aff Unit Aff Unit
spec = describe "Pickles.Prove.SideLoadedMain" do
  it "parent prove with InductivePrev (PS-compiled child, width-lifted to N2)" \_ -> do
    let pallasSrs = PallasImpl.pallasCrsCreate (1 `Int.shl` 15)
    vestaSrs <- liftEffect $ createCRS @StepField

    -- Compile the Input-mode No_recursion child. Its kimchi wrap VK
    -- (at log2 = 13, `mpv = N0` → `wrap_domains.h = 13`) becomes the
    -- runtime `wrapVk` for the side-loaded slot.
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

    -- Produce a real child b0 proof. `appInput = F zero` satisfies
    -- the rule's `self == 0` assertion.
    eChildCp <- liftEffect $ runExceptT $ childProver
      { appInput: F zero
      , prevs: unit
      , sideloadedVKs: unit
      }
    childCp0 :: CompiledProof 0 (StatementIO (F StepField) Unit) Unit Unit <- case eChildCp of
      Left e -> liftEffect $ Exc.throw ("childProver: " <> show e)
      Right cp -> pure cp

    -- Width-lift the child to the side-loaded tag's bound. The slot
    -- expects `CompiledProof 2` and `Tag _ _ 2`; the outer `mpv` is
    -- phantom on both, so `coerce` repacks the bound. Sound when the
    -- actual width (0) is `≤` the new bound (2). PS analog of OCaml
    -- `Side_loaded.Proof.of_proof`.
    let
      childCp2 :: CompiledProof 2 (StatementIO (F StepField) Unit) Unit Unit
      childCp2 = coerce childCp0

      childTag2 :: Tag (F StepField) Unit 2
      childTag2 = coerce child.tag

    -- Assemble the runtime side-loaded VerificationKey. NRR's wrap
    -- circuit at log2 = 13 → `actualWrapDomainSize = N0`; child mpv =
    -- 0 → `maxProofsVerified = N0`.
    let
      childVK :: Sideload.Bundle
      childVK = Sideload.mkBundle
        { verifierIndex: child.vks.wrap.verifierIndex
        , maxProofsVerified: N0
        , actualWrapDomainSize: N0
        }

    -- Compile the side-loaded parent.
    sideLoadedEntry <- liftEffect $ mkRuleEntry
      @1
      @Unit
      @(F StepField)
      sideLoadedMainRule
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

    -- Drive the parent prove with `InductivePrev`: parent self = 1,
    -- prev = (child input = 0, wrapped child proof, child VK). The
    -- rule's `selfCorrect = 1 + 0 == 1` holds.
    eParentCp <- liftEffect $ runExceptT $ chainProver
      { appInput: F one
      , prevs: tuple1 (InductivePrev childCp2 childTag2)
      , sideloadedVKs: childVK /\ unit
      }
    case eParentCp of
      Left e -> liftEffect $ Exc.throw ("sideloaded chainProver: " <> show e)
      Right _ -> pure unit

    true `shouldEqual` true
