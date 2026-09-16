-- | A prev slot whose wrap key arrives at prove time rather than
-- | compile time. A no-recursion child is compiled and proved, the
-- | proof is width-lifted to the side-loaded slot's bound, and the
-- | parent is proved against a `Sideload.VerificationKey` built from
-- | the child's wrap result.
-- |
-- | Both proofs are verified, the child's after a round trip, so the
-- | parent's own out-of-circuit verify path is exercised at a
-- | side-loaded slot.
module Test.Pickles.Prove.SideLoadedMain
  ( spec
  ) where

import Prelude

import Colog (LoggerT, Message, withSpan)
import Data.Either (Either(..))
import Data.Maybe (Maybe(..), fromJust)
import Data.Tuple (fst)
import Data.Tuple.Nested (Tuple1, tuple1, (/\))
import Data.Vector ((:<))
import Data.Vector as Vector
import Effect.Aff (Aff)
import Effect.Class (liftEffect)
import Effect.Exception (throw) as Exc
import Node.Process (lookupEnv)
import Partial.Unsafe (unsafePartial)
import Pickles (BranchProver(..), CompiledProof, PrevSlot(..), ProofsVerified(..), RulesCons, RulesNil, Slot, SlotProveVk(..), SlotWrapKey(..), StatementIO(..), StepField, StepRule, compileMulti, mkRuleEntry, toVerifiable, verify)
import Pickles.Sideload (mkBundle) as Sideload
import Safe.Coerce (coerce)
import Snarky.Backend.Advice (noAdvice)
import Snarky.Backend.Kimchi.ProofCache (mkProofCache)
import Snarky.Circuit.CVar (add_) as CVar
import Snarky.Circuit.DSL (F(..), FVar, SizedF, assertAny_, assertEqual_, const_, equals_, exists, true_)
import Snarky.Circuit.Kimchi.EndoMul (endo)
import Snarky.Circuit.Kimchi.EndoScalar (toFieldChecked')
import Snarky.Circuit.Kimchi.VarBaseMul (scaleFast1)
import Snarky.Curves.Class (fromInt, generator, toAffine)
import Snarky.Curves.Pasta (PallasG)
import Snarky.Data.EllipticCurve (AffinePoint(..), WeierstrassAffinePoint(..))
import Snarky.Types.Shifted (Type1(..))
import Test.Pickles.SerializeRoundTrip (mkWidthDummies, roundTripAndVerify)
import Test.Pickles.SharedSrs (SharedSrs)
import Test.Spec (SpecT, describe, it)
import Test.Spec.Assertions (shouldEqual)
import Unsafe.Coerce (unsafeCoerce)

-- | The Pallas generator in affine coordinates.
innerCurveGen :: { x :: F StepField, y :: F StepField }
innerCurveGen =
  let
    { x, y } = unsafePartial $ fromJust $ toAffine (generator :: PallasG)
  in
    { x: F x, y: F y }

-- | The child rule: asserts `self == 0`, with no prevs. Its dummy
-- | constraints exist to emit the gate kinds — `EndoMulScalar`,
-- | `VarBaseMul`, `EndoMul`, on-curve — that the child step constraint
-- | system must contain for byte parity with the reference.
noRecursionInputRule
  :: StepRule 0
       Unit
       (F StepField)
       (FVar StepField)
       Unit
       Unit
       (F StepField)
       (FVar StepField)
noRecursionInputRule _ self = do
  x <- exists (pure (F (fromInt 3) :: F StepField))
  -- `g` is allocated as a `WeierstrassAffinePoint` so that `exists`
  -- emits the on-curve assertion.
  WeierstrassAffinePoint g :: WeierstrassAffinePoint PallasG (FVar StepField) <-
    exists (pure (WeierstrassAffinePoint innerCurveGen))
  _ <- toFieldChecked' @1 (unsafeCoerce x :: SizedF 16 (FVar StepField))
  _ <- scaleFast1 @1 @5 (AffinePoint g) (Type1 x)
  _ <- scaleFast1 @1 @5 (AffinePoint g) (Type1 x)
  _ <- endo @4 @1 (AffinePoint g) (unsafeCoerce x :: SizedF 4 (FVar StepField))
  assertEqual_ self (const_ zero)
  pure
    { prevPublicInputs: Vector.nil
    , proofMustVerify: Vector.nil
    , publicOutput: unit
    }

-- | Carrier for the single child rule, at width 0 with no prevs.
type NoRecursionInputRules =
  RulesCons 0 Unit Unit RulesNil

-- | Carrier for the parent rule: one side-loaded prev slot at width 2.
type SideLoadedMainRules =
  RulesCons 1
    (Tuple1 (StatementIO (F StepField) Unit))
    (Tuple1 (Slot 2 (StatementIO (F StepField) Unit)))
    RulesNil

-- | The parent rule: asserts `1 + prev == self`, or the base case
-- | `self == 0`.
-- |
-- | `proofMustVerify` must stay the constant `true_`. A non-constant
-- | one emits about 25 extra Generic gates that constant-folding
-- | removes here, shifting the step verification key and cascading
-- | through the `step_keys` constants baked into the wrap constraint
-- | system.
sideLoadedMainRule
  :: StepRule 1
       (Tuple1 (StatementIO (F StepField) Unit))
       (F StepField)
       (FVar StepField)
       Unit
       Unit
       (F StepField)
       (FVar StepField)
sideLoadedMainRule getPrevStates self = do
  prev <- exists $ getPrevStates <#> \(StatementIO { input } /\ _) -> input
  isBaseCase <- equals_ (const_ zero) self
  selfCorrect <- equals_ (CVar.add_ (const_ one) prev) self
  assertAny_ [ selfCorrect, isBaseCase ]
  pure
    { prevPublicInputs: prev :< Vector.nil
    , proofMustVerify: true_ :< Vector.nil
    , publicOutput: unit
    }

spec :: SpecT (LoggerT Message Aff) SharedSrs Aff Unit
spec = describe "Pickles.Prove.SideLoadedMain" do
  it "parent prove with InductivePrev (PS-compiled child, width-lifted to N2)" \{ pallasSrs, vestaSrs, lagrangeCache } -> do
    cache <- liftEffect $ lookupEnv "PICKLES_PROOF_CACHE_DIR" <#> map \dir -> mkProofCache (dir <> "/SideLoadedMain.json")

    -- The child's kimchi wrap verification key becomes the runtime
    -- `wrapVk` of the parent's side-loaded slot.
    childEntry <- liftEffect $ mkRuleEntry @0 @Unit @(F StepField)
      noRecursionInputRule
      Vector.nil

    child <- withSpan "[SideLoadedMain] compile child" $ liftEffect $ compileMulti
      @NoRecursionInputRules
      @Unit
      @(F StepField)
      @1
      noAdvice
      { srs: { vestaSrs, pallasSrs }
      , debug: false
      , wrapDomainOverride: Nothing
      , proofCache: cache
      , lagrangeCache: Just lagrangeCache
      }
      (tuple1 childEntry)

    let BranchProver childProver = fst child.provers

    -- `appInput = F zero` is what the child's `self == 0` assertion
    -- needs.
    eChildCp <- withSpan "[SideLoadedMain] prove child" $ liftEffect $ childProver noAdvice
      { appInput: F zero
      , prevs: unit
      , sideloadedVKs: unit
      }
    childCp0 :: CompiledProof 0 (StatementIO (F StepField) Unit) <- case eChildCp of
      Left e -> liftEffect $ Exc.throw ("childProver: " <> show e)
      Right cp -> pure cp

    -- The slot expects `CompiledProof 2` and `Tag _ 2`, and the width
    -- is phantom on both, so `coerce` lifts the bound. Sound only
    -- because the child's actual width, 0, is at most 2.
    let
      childCp2 :: CompiledProof 2 (StatementIO (F StepField) Unit)
      childCp2 = coerce childCp0

      childTag2 = coerce child.tag

    -- The child's wrap circuit sits at domain log2 13, giving
    -- `actualWrapDomainSize = N0`; its width 0 gives
    -- `maxProofsVerified = N0`.
    let
      childVK = Sideload.mkBundle
        { verifierIndex: child.vks.wrap.verifierIndex
        , maxProofsVerified: N0
        , actualWrapDomainSize: N0
        }

    sideLoadedEntry <- liftEffect $ mkRuleEntry
      @1
      @Unit
      @(F StepField)
      sideLoadedMainRule
      (SideLoadedKey :< Vector.nil)

    parent <- withSpan "[SideLoadedMain] compile parent" $ liftEffect $ compileMulti
      @SideLoadedMainRules
      @Unit
      @(F StepField)
      @1
      noAdvice
      { srs: { vestaSrs, pallasSrs }
      , debug: false
      , wrapDomainOverride: Nothing
      , proofCache: cache
      , lagrangeCache: Just lagrangeCache
      }
      (tuple1 sideLoadedEntry)

    let BranchProver chainProver = fst parent.provers

    let dummies = mkWidthDummies pallasSrs vestaSrs

    -- The parent's prev is the reconstruction, not the original, so
    -- the prove below only succeeds if the round trip is faithful.
    childCp2' <- roundTripAndVerify dummies child.verifier childCp2

    -- Parent `self = 1` over a child whose input is 0, so the rule's
    -- `1 + prev == self` branch is the one that holds.
    eParentCp <- withSpan "[SideLoadedMain] prove parent" $ liftEffect $ chainProver noAdvice
      { appInput: F one
      , prevs: tuple1 (InductivePrev childCp2' childTag2)
      , sideloadedVKs: SideLoadedVk childVK /\ unit
      }
    parentCp <- case eParentCp of
      Left e -> liftEffect $ Exc.throw ("sideloaded chainProver: " <> show e)
      Right cp -> pure cp

    verify parent.verifier (toVerifiable parentCp) `shouldEqual` true
