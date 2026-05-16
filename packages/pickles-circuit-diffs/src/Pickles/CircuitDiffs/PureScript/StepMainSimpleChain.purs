module Pickles.CircuitDiffs.PureScript.StepMainSimpleChain
  ( compileStepMainSimpleChain
  , StepMainSimpleChainParams
  , class SimpleChainAdvice
  , getSimpleChainPrev
  ) where

-- | step_main circuit for the Simple_Chain inductive rule (N1, 1 previous proof).
-- | Delegates to the generic Pickles.Step.Main.stepMain.
-- |
-- | Reference: mina/src/lib/crypto/pickles/dump_circuit_impl.ml (step_main_simple_chain)

import Prelude

import Control.Monad.Trans.Class (lift)
import Data.Tuple.Nested (Tuple1, tuple1, (/\))
import Data.Vector (Vector, (:<))
import Data.Vector as Vector
import Effect (Effect)
import Effect.Exception (throw)
import Pickles.CircuitDiffs.PureScript.Common (StepArtifact, dummyWrapSg, mkStepArtifact, preComputeSelfStepDomainLog2)
import Pickles.Field (StepField)
import Pickles.PublicInputCommit (LagrangeBaseLookup)
import Pickles.Slots (Compiled, Slot)
import Pickles.Step.Main (RuleOutput, SlotVkBlueprintCompiled(..), stepMain)
import Pickles.Types (StatementIO)
import Snarky.Backend.Compile (compile)
import Snarky.Circuit.CVar (add_) as CVar
import Snarky.Circuit.DSL (class CircuitM, F, FVar, Snarky, assertAny_, const_, equals_, exists, not_)
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Constraint.Kimchi as Kimchi
import Snarky.Data.EllipticCurve (AffinePoint)
import Type.Proxy (Proxy(..))

type StepMainSimpleChainParams =
  { lagrangeAt :: LagrangeBaseLookup 1 StepField
  , blindingH :: AffinePoint (F StepField)
  }

-- | Application-specific advice for the Simple_Chain N1 rule.
-- |
-- | The rule allocates one previous-proof app_state field. In OCaml this is
-- | done via `exists StepField.typ ~compute:(fun () -> StepField.Constant.zero)`.
-- | In PureScript we route it through this typeclass so the SAME rule
-- | definition can be used for both compilation (Effect throws) and
-- | proving (a ReaderT-based instance returns the real previous proof's
-- | app_state).
class Monad m <= SimpleChainAdvice m where
  getSimpleChainPrev :: Unit -> m (F StepField)

-- | Compilation instance: throws if evaluated. `exists` in CircuitBuilderT
-- | discards the AsProverT entirely so the throw never fires.
instance SimpleChainAdvice Effect where
  getSimpleChainPrev _ = throw "SimpleChainAdvice.getSimpleChainPrev: not available during compilation"

-- | Simple_Chain N1 rule: self_correct = (1 + prev == self)
-- | Reference: dump_circuit_impl.ml:4390-4413
simpleChainRule
  :: forall t m
   . CircuitM StepField (KimchiConstraint StepField) t m
  => SimpleChainAdvice m
  => FVar StepField
  -> Snarky (KimchiConstraint StepField) t m (RuleOutput 1 (FVar StepField) Unit)
simpleChainRule appState = do
  prev <- exists $ lift $ getSimpleChainPrev unit
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
  runStepCompile selfLog2 =
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
      )
      Kimchi.initialState
