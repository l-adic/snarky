module Pickles.CircuitDiffs.PureScript.StepMainSimpleChainN2
  ( compileStepMainSimpleChainN2
  , StepMainSimpleChainN2Params
  ) where

-- | step_main circuit for the Simple_Chain N2 rule (2 previous proofs).
-- | Delegates to the generic Pickles.Step.Main.stepMain.
-- |
-- | Reference: mina/src/lib/crypto/pickles/dump_simple_chain_n2/dump_simple_chain_n2.ml

import Prelude

import Data.Maybe (Maybe(..))
import Data.Tuple (Tuple)
import Data.Tuple.Nested (Tuple2, tuple2, (/\))
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

type StepMainSimpleChainN2Params =
  { lagrangeAt :: LagrangeBaseLookup 1 StepField
  , blindingH :: AffinePoint (F StepField)
  }

-- | Simple_Chain N2 rule: self_correct = (1 + prev1 + prev2 == self)
-- | Both proofs have the same proof_must_verify = not is_base_case.
-- | The two previous app-states are read from the deferred prev-states
-- | getter (projected from advice; forced only inside the rule's own
-- | `exists`, so compile never touches the dummy advice).
-- | Reference: dump_simple_chain_n2.ml
simpleChainN2Rule
  :: forall t m
   . CircuitM StepField (KimchiConstraint StepField) t m
  => AsProverT StepField m
       (Tuple2 (StatementIO (F StepField) Unit) (StatementIO (F StepField) Unit))
  -> FVar StepField
  -> Snarky (KimchiConstraint StepField) t m (RuleOutput 2 (FVar StepField) Unit)
simpleChainN2Rule getPrevStates appState = do
  prev1 <- exists $ getPrevStates <#> \(StatementIO p1 /\ _) -> p1.input
  prev2 <- exists $ getPrevStates <#> \(_ /\ StatementIO p2 /\ _) -> p2.input
  isBaseCase <- equals_ (const_ zero) appState
  let proofMustVerify = not_ isBaseCase
  selfCorrect <- equals_ (CVar.add_ (CVar.add_ (const_ one) prev1) prev2) appState
  assertAny_ [ selfCorrect, isBaseCase ]
  pure
    { prevPublicInputs: prev1 :< prev2 :< Vector.nil
    , proofMustVerify: proofMustVerify :< proofMustVerify :< Vector.nil
    , publicOutput: unit
    }

compileStepMainSimpleChainN2
  :: StepMainSimpleChainN2Params -> Effect StepArtifact
compileStepMainSimpleChainN2 params = do
  -- Both prev slots are self → both FOP domain log2s = this rule's own
  -- step domain log2. Resolved via two-pass compile (mirrors OCaml
  -- `Fix_domains.domains`).
  selfLog2 <- preComputeSelfStepDomainLog2 (runStepCompile 1)
  mkStepArtifact <$> runStepCompile selfLog2
  where
  runStepCompile selfLog2 = do
    -- Throwaway capture Ref + dummy advice, mirroring `stepCompile`:
    -- compile discards every `exists` body, so the Ref stays `Nothing`
    -- and the `unsafeCoerce unit` advice is never projected.
    throwawayCaptureRef <- Ref.new Nothing
    -- `carrier` (value-side per-proof witness carrier) is not determined
    -- by `stepMain`'s var-side `StepSlotsCarrier` constraint (CircuitType
    -- has no var→value fundep), so we pin it here. Mirrors the value-side
    -- `StepSlotsCarrier` constraint in `Prove.Step.stepCompile`.
    let
      dummyAdvice
        :: StepAdvice _ _ _ _ _ _
             ( Tuple
                 ( PerProofWitness 2 1 StepIPARounds WrapIPARounds (F StepField)
                     (Type2 (SplitField (F StepField) Boolean))
                     Boolean
                 )
                 ( Tuple
                     ( PerProofWitness 2 1 StepIPARounds WrapIPARounds (F StepField)
                         (Type2 (SplitField (F StepField) Boolean))
                         Boolean
                     )
                     Unit
                 )
             )
             _
             _
      dummyAdvice = unsafeCoerce unit
    compile (Proxy @Unit) (Proxy @(Vector 67 (F StepField))) (Proxy @(KimchiConstraint StepField))
      -- Single-rule: mpvMax = len = 2, mpvPad = 0.
      ( \_ -> stepMain
          @(Tuple2 (Slot Compiled 2 1 (StatementIO (F StepField) Unit)) (Slot Compiled 2 1 (StatementIO (F StepField) Unit)))
          @(F StepField)
          @Unit
          @(F StepField)
          @( Tuple2 (StatementIO (F StepField) Unit) (StatementIO (F StepField) Unit)
          )
          @2
          @1
          @Unit
          @1
          simpleChainN2Rule
          { perSlotLagrangeAt: params.lagrangeAt :< params.lagrangeAt :< Vector.nil
          , blindingH: params.blindingH
          , perSlotFopDomainLog2s:
              (selfLog2 :< Vector.nil) :< (selfLog2 :< Vector.nil) :< Vector.nil
          , perSlotVkBlueprints: VkBlueprintShared /\ VkBlueprintShared /\ unit
          }
          dummyWrapSg
          -- Side-loaded VK carrier: two Cons slots,
          -- both compiled; carrier = `Unit /\ Unit /\ Unit`.
          (tuple2 unit unit)
          dummyAdvice
          throwawayCaptureRef
      )
      Kimchi.initialState
