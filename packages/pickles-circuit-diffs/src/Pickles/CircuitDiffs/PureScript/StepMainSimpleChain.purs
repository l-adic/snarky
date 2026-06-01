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
import Data.Tuple (Tuple)
import Data.Tuple.Nested (Tuple1, tuple1, (/\))
import Data.Vector (Vector, (:<))
import Data.Vector as Vector
import Effect (Effect)
import Effect.Ref as Ref
import Pickles.CircuitDiffs.PureScript.Common (StepArtifact, dummyWrapSg, mkStepArtifact, preComputeSelfStepDomainLog2)
import Pickles.Field (StepField)
import Pickles.PublicInputCommit (LagrangeBaseLookup)
import Pickles.Slots (Compiled, Slot)
import Pickles.Step.Advice (StepAdvice)
import Pickles.Step.Main (RuleOutput, SlotVkBlueprintCompiled(..), stepMain)
import Pickles.Step.Types (PerProofWitness)
import Pickles.Types (StatementIO(..), StepIPARounds, WrapIPARounds)
import Snarky.Backend.Compile (compile)
import Snarky.Circuit.CVar (add_) as CVar
import Snarky.Circuit.DSL (class CircuitM, AsProverT, F, FVar, Snarky, assertAny_, const_, equals_, exists, not_)
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Constraint.Kimchi as Kimchi
import Snarky.Data.EllipticCurve (AffinePoint)
import Snarky.Types.Shifted (SplitField, Type2)
import Type.Proxy (Proxy(..))
import Unsafe.Coerce (unsafeCoerce)

type StepMainSimpleChainParams =
  { lagrangeAt :: LagrangeBaseLookup 1 StepField
  , blindingH :: AffinePoint (F StepField)
  }

-- | Simple_Chain N1 rule: self_correct = (1 + prev == self)
-- | Reference: dump_circuit_impl.ml:4390-4413
simpleChainRule
  :: forall t m
   . CircuitM StepField (KimchiConstraint StepField) t m
  => AsProverT StepField m (Tuple1 (StatementIO (F StepField) Unit))
  -> FVar StepField
  -> Snarky (KimchiConstraint StepField) t m (RuleOutput 1 (FVar StepField) Unit)
simpleChainRule getPrevStates appState = do
  prev <- exists $ getPrevStates <#> \(StatementIO p1 /\ _) -> p1.input
  isBaseCase <- equals_ (const_ zero) appState
  let proofMustVerify = not_ isBaseCase
  selfCorrect <- equals_ (CVar.add_ (const_ one) prev) appState
  assertAny_ [ selfCorrect, isBaseCase ]
  pure
    { prevPublicInputs: prev :< Vector.nil
    , proofMustVerify: proofMustVerify :< Vector.nil
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
    -- `carrier` (the value-side per-proof witness carrier) is not
    -- determined by `stepMain`'s var-side `StepSlotsCarrier` constraint
    -- (CircuitType has no var→value fundep), so we pin it here. Mirrors
    -- the value-side `StepSlotsCarrier` constraint in `Prove.Step.stepCompile`.
    let
      dummyAdvice
        :: StepAdvice _ _ _ _ _ _
             ( Tuple
                 ( PerProofWitness 1 1 StepIPARounds WrapIPARounds (F StepField)
                     (Type2 (SplitField (F StepField) Boolean))
                     Boolean
                 )
                 Unit
             )
             _
             _
      dummyAdvice = unsafeCoerce unit
    compile (Proxy @Unit) (Proxy @(Vector 34 (F StepField))) (Proxy @(KimchiConstraint StepField))
      -- Axes: @prevsSpec @outputSize @inputVal @input @outputVal @output
      --       @prevInputVal @prevInput @valCarrier @mpvMax @mpvPad.
      -- Single-rule: mpvMax = len = 1, mpvPad = 0.
      ( \_ -> stepMain
          @(Tuple1 (Slot Compiled 1 1 (StatementIO (F StepField) Unit)))
          @(F StepField)
          @Unit
          @(F StepField)
          @(Tuple1 (StatementIO (F StepField) Unit))
          @1
          @1
          @Unit
          @1
          simpleChainRule
          { perSlotLagrangeAt: params.lagrangeAt :< Vector.nil
          , blindingH: params.blindingH
          , perSlotFopDomainLog2s: (selfLog2 :< Vector.nil) :< Vector.nil
          , perSlotVkBlueprints: VkBlueprintShared /\ unit
          }
          dummyWrapSg
          -- Side-loaded VK carrier: one Cons slot,
          -- compiled (Unit), no side-loaded position; carrier = `Unit /\ Unit`.
          (tuple1 unit)
          dummyAdvice
          throwawayCaptureRef
      )
      Kimchi.initialState
