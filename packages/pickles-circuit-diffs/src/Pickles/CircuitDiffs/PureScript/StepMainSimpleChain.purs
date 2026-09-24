module Pickles.CircuitDiffs.PureScript.StepMainSimpleChain
  ( compileStepMainSimpleChain
  , StepMainSimpleChainParams
  ) where

-- | step_main circuit for the Simple_Chain inductive rule (N1, 1 previous proof).
-- | Delegates to the generic Pickles.Step.Main.stepMain.
-- |
-- | Reference: mina/src/lib/crypto/pickles/dump_circuit_impl.ml (step_main_simple_chain)

import Prelude

import Data.Maybe (Maybe(..))
import Data.Tuple.Nested (Tuple1, (/\))
import Data.Vector (Vector, (:<))
import Data.Vector as Vector
import Effect (Effect)
import Effect.Ref as Ref
import Pickles.CircuitDiffs.PureScript.Common (StepArtifact, dummyWrapSg, mkStepArtifact, preComputeSelfStepDomainLog2)
import Pickles.Field (StepField)
import Pickles.PublicInputCommit (LagrangeBaseLookup)
import Pickles.Slots (Slot)
import Pickles.Step.Main (RuleOutput, SlotVkBlueprint(..), stepMain)
import Pickles.Step.Slots (PrevStatement(..), PrevValues, prevValues, toPrevs)
import Pickles.Types (StatementIO(..))
import Snarky.Backend.Advice (noAdvice)
import Snarky.Backend.Compile (compile)
import Snarky.Circuit.CVar (add_) as CVar
import Snarky.Circuit.DSL (AsProver, F, FVar, Snarky, assertAny_, const_, equals_, exists, not_)
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Curves.Class (class PrimeField)
import Snarky.Data.EllipticCurve (AffinePoint)
import Type.Proxy (Proxy(..))
import Unsafe.Coerce (unsafeCoerce)

type StepMainSimpleChainParams =
  { lagrangeAt :: LagrangeBaseLookup 1 StepField
  , blindingH :: AffinePoint (F StepField)
  }

-- | The rule's one self prev slot, at width 1.
type SimpleChainPrevsSpec = Tuple1 (Slot 1 (StatementIO (F StepField) Unit))

-- | Simple_Chain N1 rule: self_correct = (1 + prev == self)
-- | Reference: dump_circuit_impl.ml:4390-4413
simpleChainRule
  :: forall r
   . PrimeField StepField
  => AsProver StepField r (PrevValues SimpleChainPrevsSpec)
  -> FVar StepField
  -> Snarky StepField (KimchiConstraint StepField) r (RuleOutput SimpleChainPrevsSpec Unit)
simpleChainRule getPrevStates appState = do
  prev <- exists $ getPrevStates <#> prevValues <#> \(StatementIO p1 /\ _) -> p1.input
  isBaseCase <- equals_ (const_ zero) appState
  let proofMustVerify = not_ isBaseCase
  selfCorrect <- equals_ (CVar.add_ (const_ one) prev) appState
  assertAny_ [ selfCorrect, isBaseCase ]
  pure
    { prevs: toPrevs $
        PrevStatement { publicInput: StatementIO { input: prev, output: unit }, proofMustVerify }
          /\ unit
    , publicOutput: unit
    }

compileStepMainSimpleChain
  :: StepMainSimpleChainParams -> Effect StepArtifact
compileStepMainSimpleChain params = do
  -- Self-prev rule: the slot's prev source is `self`, so its FOP step
  -- domain log2 = this rule's own step domain log2 — a circular
  -- dependency resolved via two-pass (shape pass + real pass) compile.
  -- Mirrors OCaml `Fix_domains.domains` (compile.ml).
  selfLog2 <- preComputeSelfStepDomainLog2 (runStepCompile 1)
  mkStepArtifact <$> runStepCompile selfLog2
  where
  runStepCompile selfLog2 = do
    throwawayCaptureRef <- Ref.new Nothing
    let
      dummyAdvice = unsafeCoerce unit
    compile noAdvice (Proxy @Unit) (Proxy @(Vector 34 (F StepField))) (Proxy @(KimchiConstraint StepField))
      -- Axes: @prevsSpec @inputVal @outputVal @valCarrier @mpvMax @nd
      --       @cell.
      -- Single-rule: mpvMax = len = 1, mpvPad = 0.
      ( \_ -> stepMain
          @SimpleChainPrevsSpec
          @(F StepField)
          @Unit
          @(Tuple1 (StatementIO (F StepField) Unit))
          @1
          @1
          simpleChainRule
          { blindingH: params.blindingH
          , perSlotFopDomainLog2s: (selfLog2 :< Vector.nil) :< Vector.nil
          , perSlotNumChunks: 1 :< Vector.nil
          , perSlotVkBlueprints: BlueprintSelf params.lagrangeAt :< Vector.nil
          }
          dummyWrapSg
          dummyAdvice
          throwawayCaptureRef
      )
